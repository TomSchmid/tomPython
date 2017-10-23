#!/usr/bin/env python
# -*- coding: utf-8 -*-
'''
VMware VRealize Automation (vRA) Inventory Script
=======================
Retrieve information about virtual machines from a vRA, though a
vRO ( vRealize Orchestrator ) server.

    Copyright (C) 2017  SovLabs - A Division of Sovereign Systems, LLC

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.

This script will attempt to read configuration from an YAML file with the same
base filename if present, or `vra.yaml` if not.  It is possible to create
symlinks to the inventory script to support multiple configurations, e.g.:
* `vra.py` (this script)
* `vra_.yaml` (default configuration, will be read by `vra_profile.py`)
* `vra_test.py` (symlink to `vra.py`)
* `vra_test.yaml` (test configuration, will be read by `vra_test.py`)
* `vra_other.py` (symlink to `vra.py`, will read `vra.yaml` since no `vra_other.yaml` exists)

The path to an YAML file may also be specified via the `VRA_YAML` environment
variable, in which case the filename matching rules above will not apply.
Host and authentication parameters may be specified via the `VRA_VRO_HOST`,
`VRA_VRO_PORT`, `VRA_VRO_USER` and `VRA_VRO_PASSWORD` environment variables;
these options will take precedence over options present in the YAML file.

In vra.yaml, a value for atow_inv_profile_name must be provided and be the same
as an existing SovLabs AnsibleTowerInventoryProfile.
'''

from __future__ import print_function

import collections
import json
import optparse
import os
import sys
import requests
from requests.packages.urllib3.exceptions import InsecureRequestWarning
import six
import time
import logging
import re

from yaml import load, dump
try:
    from yaml import CLoader as Loader, CDumper as Dumper
except ImportError:
    from yaml import Loader, Dumper

class VraInventory(object):

    def __init__(self):

        self.config = {}
        if os.environ.get('VRA_YAML', ''):
            config_files = [os.environ['VRA_YAML']]
        else:
            config_files = [os.path.abspath(sys.argv[0]).rstrip('.py') + '.yaml', 'vra.yaml']
        for config_file in config_files:
            if os.path.exists(config_file):
                stream = file(config_file, 'r')
                self.config = load(stream)
                stream.close()
                break
            else:
                print("Unable to find config file: " + config_file)
                exit(1)

        self.page = 0
        self.last_run = None
        self.last_run_paged = None
        self.more_machines = True
        self.group_separator = None
        self.logging_file = None
        self.deprov_host_names_json = None

       # Read configuration information from vra environment variables
        # (if set), otherwise from INI file.
        self.vro_host = os.environ.get('VRA_VRO_HOST')
        if not self.vro_host and "vro_host" in self.config:
            self.vro_host = self.config["vro_host"]

        self.vro_port = os.environ.get('VRA_VRO_PORT')
        if not self.vro_port and "vro_port" in self.config:
            self.vro_port = self.config["vro_port"]

        self.vro_user = os.environ.get('VRA_VRO_USER')
        if not self.vro_user and "vro_user" in self.config:
            self.vro_user = self.config["vro_user"]

        self.vro_password = os.environ.get('VRA_VRO_PASSWORD')
        if not self.vro_password and "vro_password" in self.config:
            self.vro_password = self.config["vro_password"]

        self.sslcheck = os.environ.get('VRA_SSLCHECK')
        if not self.sslcheck and "sslcheck" in self.config:
            self.sslcheck = self.config["sslcheck"]

        if isinstance(self.sslcheck, six.string_types):
            if self.sslcheck.lower() in ['no', 'false']:
                self.sslcheck = False
            else:
                self.sslcheck = True

        if "logging_file" in self.config and self.config["logging_file"] is not None:
            import datetime
            dt = str(datetime.datetime.now())
            self.logging_file = self.config["logging_file"]
            logfile_name = self.config["logging_file"] +dt
            logging.basicConfig(filename=logfile_name, level=logging.DEBUG)
            logging.debug('Found logging file!  Doing logging.')

        #
        # Verify Configuration Values are set
        #
        if self.sslcheck is None:
            self.sslcheck = False

        if self.vro_host is None:
            print("You must supply the vro_host in the vra.yaml or as an environment variable")
            exit(1)

        if self.vro_port is None:
            print("You must supply the vro_port in the vra.yaml or as an environment variable")
            exit(1)

        if self.vro_user is None:
            print("You must supply the vro_user in the vra.yaml or as an environment variable")
            exit(1)

        if self.vro_password is None:
            print("You must supply the vro_password in the vra.yaml or as an environment variable")
            exit(1)

        if self.config["inventory_workflow_id"] is None:
            print("You must supply the inventory_workflow_id in the vra.yaml or as an environment variable")
            exit(1)

        if self.config["deprov_workflow_id"] is None:
            print("You must supply the deprov_workflow_id in the vra.yaml or as an environment variable")
            exit(1)

        if self.config["cache_max_age"] is None:
            print("You must supply the cache_max_age in the vra.yaml or as an environment variable")
            exit(1)

        if self.config["cache_dir"] is None:
            print("You must supply the cache_dir in the vra.yaml or as an environment variable")
            exit(1)

        if self.config["cache_machine_build_time_offset"] is None:
            print("You must supply the cache_machine_build_time_offset in the vra.yaml or as an environment variable")
            exit(1)

    def update_child_groups(self, host, grppath, inv):
        if len(grppath) > 0:
            if grppath[0] not in inv:
                inv[grppath[0]] = {"hosts": [host], "vars": {}}
            else:
                if host not in inv[grppath[0]]["hosts"]:
                    inv[grppath[0]]["hosts"].append(host)

            #Add the child to the group
            if len(grppath) > 1:
                if "children" in inv[grppath[0]]:
                    if grppath[1] not in inv[grppath[0]]["children"]:
                        inv[grppath[0]]["children"].append(grppath[1])
                else:
                    inv[grppath[0]]["children"] = [grppath[1]]

        #Remove the parent groupm, and do it all over again if there are more child groups
        grppath.pop(0)
        if len(grppath) > 0:
            self.update_child_groups(host, grppath, inv)

    def get_inventory(self, hostname, clearcache):

        # Get the cache first
        if not clearcache:
            cache = self.get_cache("vra_cache.json")
        else:
            cache = None

        # Call the vro Workflow until there are no more machines
        fullresults = {}
        while self.more_machines:
            self.page += 1 # Must come before create_payload()
            payload = self.create_payload(hostname)
            result = self.run_vro_workflow(payload)
            result = json.loads(result)
            fullresults.update(result)

        # if we have a cache and we got a result from vRO, merge them together, with vRO latest results winning
        if cache is not None:
            logging.debug('We have cache.')
            cache.update(fullresults)
            result = cache
        else:
            logging.debug('Did not have cache, using results')
            result = fullresults

        #delete_cache_list = json.dumps(delete_cache_vms)['vmTokens']
        #logging.debug('LIST of vms to delete from cache.')
        #for delete_cache in delete_cache_vms['vmTokens']:
        #    logging.debug ('Delete(', delete_cache['hostName'], ')')

        delete_cache_vms = '{"vmTokens": []}'
        delete_cache_vms = json.loads(delete_cache_vms)
        # Here, we weed out deprovisioned VMs that came in from DynamicInventory/AnsibleDeprovVmCache.
        # The delete_cache_vms will be passed back to a workflow to make sure we only delete the ones that got
        # deleted out of the vRO Resource "Ansible DeprovVM Cache" and leave the rest.
        #result, delete_cache_vms = self.remove_deprov_vms(self.deprov_host_names_json, result, delete_cache_vms)
        result, delete_cache_vms = self.remove_deprov_vms(self.deprov_host_names_json, result, delete_cache_vms)
        if len(delete_cache_vms['vmTokens']) > 0:
            payload = self.create_deprov_payload(delete_cache_vms['vmTokens'])
            wf_result = self.run_deprov_workflow(payload)

        # Cache the results
        self.put_cache("vra_cache.json", result)

        if hostname is not None:
            return result.get(hostname).get("properties")

        # Build the inventory object
        inv = {"all": {"hosts": []}}
        inv["_meta"] = {"hostvars": {}}
        for host, data in result.items():
            inv["_meta"]["hostvars"][host] = data["properties"]
            inv["all"]["hosts"].append(host)
            for group in data["groups"]:
                grppath = group.split(self.group_separator)
                self.update_child_groups(host, grppath, inv)
        return inv

    def run_vro_workflow(self, payload):
        url = 'https://' + self.vro_host + ':' + str(self.vro_port) + '/vco/api/workflows/' + \
              self.config['inventory_workflow_id'] + '/executions/'
        vro_auth = requests.auth.HTTPBasicAuth(self.vro_user, self.vro_password)
        headers = {'Content-Type': 'application/json', 'Accept': 'application/json'}
        if not self.sslcheck:
            requests.packages.urllib3.disable_warnings()
        r = requests.post(url, data=payload, verify=False, auth=vro_auth, headers=headers)
        result = {}
        if r.status_code == 202:
            location = r.headers['Location']
            while True:
                workflow_status = requests.get(location, verify=False, auth=vro_auth, headers=headers)
                status = workflow_status.json()
                logging.debug('After request, state[%s]', status['state'])
                if status['state'] == "running":
                    time.sleep(5)
                    continue
                elif status['state'] == "failed":
                    print("ERROR running inventory workflow: " + status['content-exception'])
                    exit(211)
                elif status['state'] == "completed":
                    output_params = status['output-parameters']
                    result = output_params[0]['value']['string']['value']
                    self.more_machines = output_params[2]['value']['boolean']['value']
                    self.group_separator = output_params[3]['value']['string']['value']
                    self.deprov_host_names_json = output_params[6]['value']['string']['value']
                    # TOM
                    logging.debug('After request, more_machines[%d] page[%d]', self.more_machines, self.page)
                    logging.debug('Result==>%s<==END', result)

                    if self.page == 1:
                        self.last_run_paged = output_params[1]['value']['string']['value']
                        if self.last_run_paged is not None:
                            logging.debug('In run_vro_workflow(), setting last_run_paged to [%s]', self.last_run_paged)
                        else:
                            logging.debug('In run_vro_workflow(), setting last_run_paged to [null]')

                    if self.more_machines is False:
                        logging.debug('More machines is false')
                        if self.page > 1:
                            self.last_run = self.last_run_paged
                            if self.last_run is not None:
                               logging.debug('In run_vro_workflow() for page > 1, setting last_run to [%s]', self.last_run_paged)
                            else:
                               logging.debug('In run_vro_workflow() for page > 1, setting last_run to [null]')

                        else:
                            self.last_run = output_params[1]['value']['string']['value']
                            if self.last_run is not None:
                               logging.debug('In run_vro_workflow() for page == 1, setting last_run to [%s]', self.last_run)
                            else:
                               logging.debug('In run_vro_workflow() for page == 1, setting last_run to [null]')

                else:
                    print("Inventory Workflow finished with unsupported status " + status['state'])
                    exit(400)
                break
        else:
            print(r)

        return result

    def create_payload(self, hostname):
        #logging.debug('In create_payload, host[', hostname, "]")
        logging.debug('Zeroing out hostname to see what happens!')
        hostname = ''
        parameters = {
            "parameters": []
        }

        pgp = {
                    "value": {
                        "number": {
                            "value": self.page
                        }
                    },
                    "type": "number",
                    "name": "page",
                    "scope": "local"
        }
        parameters["parameters"].append(pgp)

        if hostname is not None:
            holder = {"value": {"string": {"value": hostname}},
                      "type": "string", "name": "hostname", "scope": "local"}
            parameters["parameters"].append(holder)

        if "tenant" in self.config and len(self.config["tenant"]) > 0:
            holder = {"value": {"string": {"value": self.config["tenant"]}},
                      "type": "string", "name": "tenant", "scope": "local"}
            parameters["parameters"].append(holder)

        if "cache_max_age" in self.config and self.config["cache_max_age"] > 0 \
                and "cache_dir" in self.config and self.last_run is not None:
            holder = {"value": {"string": {"value": self.last_run}},
                      "type": "string", "name": "startDate", "scope": "local"}
            parameters["parameters"].append(holder)
            logging.debug('Building startDate')
        else:
            logging.debug('Could NOT build startDate!')

        if "cache_machine_build_time_offset" in self.config and self.config["cache_machine_build_time_offset"] >= 0:
            holder = {"value": {"number": {"value": self.config["cache_machine_build_time_offset"]}},
                      "type": "number", "name": "startDateOffset", "scope": "local"}
            parameters["parameters"].append(holder)
            logging.debug('Building startDateOffset')
        else:
            logging.debug('Could NOT build startDateOffset!')

        if "atow_inv_profile_name" in self.config and len(self.config["atow_inv_profile_name"]) > 0:
	    holder = {"value": {"string": {"value": self.config["atow_inv_profile_name"]}},
	             "type": "string", "name": "atowInvProfileName", "scope": "local"}
            parameters["parameters"].append(holder)

        return json.dumps(parameters)

    def put_cache(self, name, value):
        #
        # Saves the value to cache with the name given.
        #
        logging.debug('In put_cache(), start...')
        if "cache_dir" in self.config:
            logging.debug('In put_cache(), first clause')
            cache_dir = os.path.expanduser(self.config["cache_dir"])
            if not os.path.exists(cache_dir):
                os.makedirs(cache_dir)
            cache_file = os.path.join(cache_dir, name)
            if self.last_run is not None:
                logging.debug('In put_cache(), last_run[%s]', self.last_run)
            else:
                logging.debug('In put_cache(), last_run[null]')

            cache_data = {"last_run": self.last_run, "values": value}
            with open(cache_file, 'w') as cache:
                json.dump(cache_data, cache)
        else:
            logging.debug('In put_cache(), cache_dir not in self.config')


    def get_cache(self, name, default=None):
        #
        # Retrieves the value from cache for the given name.
        #
        if "cache_dir" in self.config:
            cache_dir = os.path.expanduser(self.config["cache_dir"])
            cache_file = os.path.join(cache_dir, name)
            if os.path.exists(cache_file):
                if self.config["cache_max_age"] is not None:
                    cache_max_age = self.config["cache_max_age"]
                else:
                    cache_max_age = 0
                cache_stat = os.stat(cache_file)

                # Check the cache file creation date and load it if it is not past the expiration time
                if cache_max_age > 0 and (cache_stat.st_ctime + cache_max_age) < time.time():
                    if cache_file is not None:
                       logging.debug('Removing the cache file at[' +cache_file +']')
                    else:
                       logging.debug('Removing the cache file at[null]')

                    # remove the cache file if it is expired
                    os.remove(cache_file)
                else:
                    with open(cache_file) as cache:
                        js = json.load(cache)
                        if "last_run" in js:
                            self.last_run = js["last_run"]
                            if self.last_run is not None:
                                logging.debug('In GET_cache(), setting last_run to [%s]', self.last_run)
                            else:
                                logging.debug('In GET_cache(), setting last_run to [null]')
                        if "values" in js:
                            return js["values"]
        return

    def remove_deprov_vms(self, deprov_vm_str, results_dict, delete_cache_vms):
        #
        # Deletes occurrences of deprov_vm_str from results_dict
        #
        logging.debug('Entering into remove_deprov_vms')
        logging.debug('\n\ndeprov_vm_str==>' +deprov_vm_str +'<==END')
        logging.debug('\n\nresults_dict ==>' +json.dumps(results_dict) +'<==END\n\n')

        # The deprov_vm_str comes to us from vRO without proper quotes (why?).  Add them.
        deprov_vm_str = re.sub('([{,:])(\w+)([},:])', '\\1\"\\2\"\\3', deprov_vm_str)
        deprov_vm_list = json.loads(deprov_vm_str)['vmTokens']

        for deprov_vm in deprov_vm_list:
            if deprov_vm['hostName'] in results_dict:
                del results_dict[deprov_vm['hostName']]
                logging.debug('Adding host to erase list(' +deprov_vm['hostName'] +')')
                delete_cache_vms['vmTokens'].append({'hostName' : deprov_vm['hostName'], 'inventoryName' : deprov_vm['inventoryName']})
                logging.debug('Done adding host to erase list')

        logging.debug('Returning from remove_deprov_vms')
        return results_dict, delete_cache_vms

    def create_deprov_payload(self, delete_cache_vms):
        parameters = {
            "parameters": []
        }
        pgp = {
                    "value": {
                        "string": {
                            "value": json.dumps(delete_cache_vms) #self.page
                        }
                    },
                    "type": "string",
                    "name": "vmTokens",
                    "scope": "local"
        }
        parameters["parameters"].append(pgp)

        return json.dumps(parameters)

    def run_deprov_workflow(self, payload):
        url = 'https://' + self.vro_host + ':' + str(self.vro_port) + '/vco/api/workflows/' + \
              self.config['deprov_workflow_id'] + '/executions/'
        vro_auth = requests.auth.HTTPBasicAuth(self.vro_user, self.vro_password)
        headers = {'Content-Type': 'application/json', 'Accept': 'application/json'}
        if not self.sslcheck:
            requests.packages.urllib3.disable_warnings()

        r = requests.post(url, data=payload, verify=False, auth=vro_auth, headers=headers)
        result = {}
        if r.status_code == 202:
            return 1
        else:
            return 0

class MultiDict(collections.OrderedDict):
    def __setitem__(self, key, value):
        if key.endswith('[]'):
            key = key[:-2]
            super(MultiDict, self).setdefault(key, []).append(value)
        else:
            super(MultiDict, self).__setitem__(key, value)

def main():
    parser = optparse.OptionParser()
    parser.add_option('--list', action='store_true', dest='list',
                      default=False, help='Output inventory groups and hosts')
    parser.add_option('--host', dest='host', default=None, metavar='HOST',
                      help='Output variables only for the given hostname')
    # Additional options for use when running the script standalone, but never
    # used by Ansible.
    parser.add_option('--pretty', action='store_true', dest='pretty',
                      default=False, help='Output nicely-formatted JSON')
    parser.add_option('--clear', action='store_true', dest='clearcache')
    options, args = parser.parse_args()

    vra_inventory = VraInventory()
    inventory = vra_inventory.get_inventory(options.host, options.clearcache)

    json_kwargs = {}
    if options.pretty:
        json_kwargs.update({'indent': 4, 'sort_keys': True})
    json.dump(inventory, sys.stdout, **json_kwargs)


if __name__ == '__main__':
    main()

