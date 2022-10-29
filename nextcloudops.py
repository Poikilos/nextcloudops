#!/usr/bin/env python3
'''
nextcloudops
------------
Website: https://github.com/poikilos/nextcloudops
Author: Jake "Poikilos" Gustafson

Delete Nextcloud trash in a fine-grained manner, and do other neat
things using the Nextcloud WebDav API directly. This program
circumvents the client.clean method of webdavclient3 (webdav3.client
submodule) by removing the leading "/".

WARNING: This script stores the last used unencrypted password in
{nextcloudwebdev}. To change the username, password or host, you must
edit the file manually or remove it and the next run of this (as a main
script rather than as a module) will ask you for the information again.

See also <https://pypi.org/search/?q=nextcloud> for more extensive
ways to use Nextcloud through Python.

pyncclient is based on pyocclient but is for Nextcloud and doesn't
maintain compatibility with ownCloud. The new module name is
nextcloud_client. It doesn't seem to delete files, so this script uses
webdavclient3 instead. However, a minimal pyncclient wrapper class is
included.


Options:
--scrub-scribus      Remove {scribus_autosaves} from trash (If you leave
                     Scribus open with autosave turned on, it will keep
                     adding and deleting these files so Nextcloud will
                     have *many* of them stored, especially if you
                     leave the program open for a long time!
'''
from __future__ import print_function
import sys
import os
import copy
import json
import xml
import xml.etree.ElementTree as ET
import re
from xml.etree.ElementTree import XMLParser
# python3 -m pip install webdavclient3
# ^ not imported until used in the function further down
# python3 -m pip install --user pyncclient
# python3 -m pip install --user requests # as per https://pypi.org/project/pyncclient/

if sys.version_info.major < 3:
    input = raw_input

verbosity = 0

verbosity_levels = [True, False, 0, 1, 2]


def set_verbosity(verbosity_level):
    global verbosity
    if verbosity_level not in verbosity_levels:
        raise ValueError(
            "verbosity_level must be one of: {}"
            "".format(verbosity_levels)
        )
    verbosity = verbosity_level


for argI in range(1, len(sys.argv)):
    arg = sys.argv[argI]
    if arg.startswith("--"):
        if arg == "--verbose":
            verbosity = 1
        elif arg == "--debug":
            verbosity = 2


def get_verbosity():
    return verbosity


def echo0(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)


def echo1(*args, **kwargs):
    if verbosity < 1:
        return
    print(*args, file=sys.stderr, **kwargs)


def echo2(*args, **kwargs):
    if verbosity < 2:
        return
    print(*args, file=sys.stderr, **kwargs)


DEFAULT_OPTIONS = {
 'webdav_hostname': "",
 'webdav_login':    "",
 'webdav_password': ""
}

SCRIBUS_AUTOSAVES = {
    r'.*\_autosave_.*\.sla',
    r'.*\_autosave_.*\.sla\..*',
    r'.*\.sla.autosave',
    r'.*\.autosave',
}


HOME = os.environ.get("HOME")
if HOME is None:
    HOME = os.environ.get("USERPROFILE")

MY_CONF_DIR = os.path.join(HOME, ".config", "nextcloudops")
MY_CONF = os.path.join(MY_CONF_DIR, "nextcloudops.json")
if not os.path.isdir(MY_CONF_DIR):
    os.makedirs(MY_CONF_DIR)

options = None

OPTIONS_HELP = {
 'webdav_hostname': " (including https:// and /nextcloud if those are correct)",
 'webdav_login':    " (user)",
 'webdav_password': ' (will be stored in plain text at "{}")'.format(MY_CONF)
}

def usage():
    echo0(__doc__.format(
        nextcloudwebdev=MY_CONF_DIR,
        scribus_autosaves=SCRIBUS_AUTOSAVES,
    ))


def load_options():
    results = None
    try:
        if os.path.isfile(MY_CONF):
            with open(MY_CONF, 'r') as f:
                print('* reading "{}"'.format(MY_CONF))
                results = json.load(f)
    except json.decoder.JSONDecodeError as ex:
        print('"{}" is incorrectly formatted. Remove it if you want to rewrite it.'.format(MY_CONF))
        raise ex
    return results


def save_options():
    with open(MY_CONF, 'w') as f:
        json.dump(options, f, indent=2)


options = load_options()
if options is None:
    options = {}


class DAVNode:
    def __init__(self, tag, parent):
        self.tag = tag
        # self.attrs = attrs  # always {} (blank) for WEBDAV
        self.data = None
        self.children = []
        self.parent = parent

    def get(self, tag):
        '''
        Get child DAVNode.
        '''
        for child in self.children:
            if child.tag == tag:
                return child
        return None

    def get_data(self, tag):
        '''
        Get child DAVNode's data.
        '''
        child = self.get(tag)
        if child is not None:
            return child.data
        return None


# See <https://stackoverflow.com/questions/5226386/
#   parsing-xml-in-python-using-a-custom-element-class>
class DAVXMLParser:
    # (xml.etree.ElementTree.XMLParser)
    # maxDepth = 0
    depth = 0
    verbose = True
    tab = "  "
    # ^ See <https://docs.python.org/3/library/xml.etree.elementtree.html#xmlparser-objects>
    def start(self, tag, attrs):
        '''
        An opening tag is found.
        attrs is always {} in WEBDAV.'''
        original_tag = tag
        tag = tag.replace("{DAV:}", "d:")
        if not hasattr(self, "stack"):
            # self.davtree = []
            self.davroot = DAVNode(None, None)
            self.stack = []
            self.parent = self.davroot
        response = DAVNode(tag, self.parent)
        self.stack.append(response)
        self.parent.children.append(response)
        self.parent = response
        # self.davtree.append(response)
        self.indent = self.depth*self.tab
        echo2(self.indent+"TAG={} ATTRS={} len(self.stack)={}".format(tag, attrs, len(self.stack)))
        self.depth += 1
        self.indent = self.depth*"  "

    def end(self, tag):
        '''Closing tag is found.'''
        tag = tag.replace("{DAV:}", "d:")
        echo2(self.indent+"END {}".format(tag))
        self.parent = self.parent.parent
        expected = None
        self.depth -= 1
        if len(self.stack) > 0:
            expected_tag = self.stack[-1].tag
            if tag != expected_tag:
                echo2(self.indent+"closing {} automatically".format(expected_tag))
                del self.stack[-1]
                # See if it is a self-closing tag.
                expected_tag = self.stack[-1].tag
                self.depth -= 1
                self.parent = self.parent.parent
                if tag != expected_tag:
                    raise SyntaxError("{} was expected but got {}".format(expected_tag, tag))
            del self.stack[-1]
        else:
            echo2(self.indent+"  WARNING: unexpected end tag={}".format(tag))

        # if len(self.stack) < 1:
        #     self.parent = self.davroot
        # else:
        #     self.parent = self.stack[-1]
        self.indent = self.depth*self.tab
        # self.davtags

    def data(self, data):
        '''Data is found.'''
        if len(data.strip()) == 0:
            return
        self.indent = self.depth*"  "
        echo2(self.indent+"DATA: {}".format(data))
        if len(self.stack) < 1:
            print(self.indent+"  WARNING: untagged data={}".format(data))
        else:
            self.stack[-1].data = data.strip()

    def close(self):
        '''end of parse'''
        echo2(self.indent+"CLOSE")
        pass


# trash (skipping several; The reason for 404's is unknown):
example_trash = '''<?xml version="1.0"?>
<d:multistatus
	xmlns:d="DAV:"
	xmlns:s="http://sabredav.org/ns"
	xmlns:oc="http://owncloud.org/ns"
	xmlns:nc="http://nextcloud.org/ns">
	<d:response>
		<d:href>/nextcloud/remote.php/dav/trashbin/redacted/trash/</d:href>
		<d:propstat>
			<d:prop>
				<d:resourcetype>
					<d:collection/>
				</d:resourcetype>
			</d:prop>
			<d:status>HTTP/1.1 200 OK</d:status>
		</d:propstat>
	</d:response>
	<d:response>
		<d:href>/nextcloud/remote.php/dav/trashbin/redacted/trash/Blender%202.81%20project.blend1.d1614292530</d:href>
		<d:propstat>
			<d:prop>
				<d:getlastmodified>Thu, 25 Feb 2021 22:35:30 GMT</d:getlastmodified>
				<d:getcontentlength>1919620</d:getcontentlength>
				<d:resourcetype/>
				<d:getetag>1614292530</d:getetag>
				<d:getcontenttype>application/octet-stream</d:getcontenttype>
			</d:prop>
			<d:status>HTTP/1.1 200 OK</d:status>
		</d:propstat>
		<d:propstat>
			<d:prop>
				<d:quota-used-bytes/>
				<d:quota-available-bytes/>
			</d:prop>
			<d:status>HTTP/1.1 404 Not Found</d:status>
		</d:propstat>
	</d:response>
	<d:response>
		<d:href>/nextcloud/remote.php/dav/trashbin/redacted/trash/The%20Path%20of%20Resistance_autosave_08_08_2021_02_23.sla.d1628404390</d:href>
		<d:propstat>
			<d:prop>
				<d:getlastmodified>Sun, 08 Aug 2021 06:33:10 GMT</d:getlastmodified>
				<d:getcontentlength>4416353</d:getcontentlength>
				<d:resourcetype/>
				<d:getetag>1628404390</d:getetag>
				<d:getcontenttype>application/octet-stream</d:getcontenttype>
			</d:prop>
			<d:status>HTTP/1.1 200 OK</d:status>
		</d:propstat>
		<d:propstat>
			<d:prop>
				<d:quota-used-bytes/>
				<d:quota-available-bytes/>
			</d:prop>
			<d:status>HTTP/1.1 404 Not Found</d:status>
		</d:propstat>
	</d:response>
</d:multistatus>
'''

class WebDav3Mgr:
    '''
    Access a webdav service using the webdavclient3 project (the
    webdav3 module).

    Public properties:
    api_route -- normally /remote.php/dav for Nextcloud
    webdav_hostname -- options['webdav_hostname'] (without api_route)
    webdav_hostname_and_route -- options['webdav_hostname'] with
        api_route appended.
    user -- is set to options.get('webdav_login')
    password -- is set to options.get('webdav_password')
    '''
    def __init__(self, test_xml=None, api_route="/remote.php/dav"):
        '''
        Keyword arguments:
        test_xml -- If test is not None, no connection will occur and
            self.client will be None.
        api_route -- The path, starting with slash, relative to
            options['webdav_hostname']. The resulting path will be
            stored in self.webdav_options['webdav_hostname']
        '''
        self.api_route = api_route
        self.client = None

        webdav_options = copy.deepcopy(options)
        self.webdav_hostname = webdav_options['webdav_hostname']
        self.user = options.get('webdav_login')
        webdav_options['webdav_hostname'] += api_route
        self.password = options.get('webdav_password')
        self.webdav_hostname_and_route = webdav_options['webdav_hostname']

        if test_xml is not None:
            return
        import webdav3
        from webdav3.client import Client
        echo0("* using {}".format(os.path.realpath(webdav3.__file__)))
        # self.host_and_api_route = webdav_options['webdav_hostname']
        self.client = Client(webdav_options)
        # self.client.verify = False # To not check SSL certificates (Default = True)

    def get_rel_from_partial_url(self, partial_url):
        api_route_i = partial_url.find(self.api_route)
        if api_route_i < 0:
            echo0("Error: {} does not contain the api_route {}"
                  "".format(partial_url, self.api_route))
            return None
        return partial_url[api_route_i+len(self.api_route):]

    def delete(self, path):
        '''
        Sequential arguments:
        path -- The path should contain the api_route but that may be
            preceeded by anything. The first instance of api_route will
            be assumed to be the part to start after. The part after
            that will be appended to self.webdav_hostname_and_route
            for the DELETE request (See <https://docs.nextcloud.com/
            server/19/developer_manual/client_apis/WebDAV/basic.html
            #deleting-files-and-folders-rfc4918>).
        '''
        rel_url = self.get_rel_from_partial_url(path)
        if rel_url is None:
            echo0("Error: {} is not in {}.".format(self.api_route, path))
            return 1
        abs_url = self.webdav_hostname_and_route + rel_url
        # echo0("DELETE {}".format(abs_url))
        # such as <https://example.com/nextcloud/remote.php/dav/
        # trashbin/redacted/trash/
        # The%20Path%20of%20Resistance_autosave_08_08_2021_02_23.sla.d1628404390>
        echo0("path={}".format(path))
        echo0("rel_url={}".format(rel_url))
        try_path = rel_url
        parts = self.webdav_hostname.split("/")
        #^  ['https:', '', 'example.com', 'nextcloud']
        main_route = None
        # <> says to delete files like:
        #   DELETE remote.php/dav/files/user/path/to/file
        #   Therefore clean up the path:
        remote_path = path
        if len(parts) >= 4:
            main_route = "/" + "/".join(parts[3:])
            echo2("main_route={}".format(main_route))
            # ^ such as "/nextcloud"
            main_route_slash = main_route + "/"
            if remote_path.startswith(main_route_slash):
                remote_path = remote_path[len(main_route_slash):]
        echo0("DELETE {}".format(remote_path))
        result = None
        # result = self.client.clean(remote_path)
        # Clean just does:
        # urn = Urn(remote_path)
        # self.execute_request(action='clean', path=urn.quote())
        # ^ always prepends / so:
        from webdav3.urn import Urn
        urn = Urn(remote_path)
        # echo0("urn={}".format(urn.quote()))
        result = self.client.execute_request(action='clean', path=urn.quote()[1:])
        echo0("result: {}".format(result))  # "<Response [200]>"

    def get_trash(self, test_xml=None):
        '''
        Get a list of the items in trash.

        Returns:
        A list of URLs including the leading /nextcloud or anything
        else after the domain, even if webdav_hostname was set to
        something ending with that.
        '''
        results = None
        # raise NotImplementedError("list is not supported, so use connect_pyncclient instead.")
        # client.session.proxies(...) # To set proxy directly into the session (Optional)
        # client.session.auth(...) # To set proxy auth directly into the session (Optional)
        # client.execute_request("mkdir", 'directory_name')
        # based on text from <https://pypi.org/project/webdavclient3/>:
        '''
        Webdav API is a set of webdav actions of work with cloud storage.
        This set includes the following actions: check, free, info, list,
        mkdir, clean, copy, move, download, upload, publish and unpublish.
        '''
        target = DAVXMLParser()
        parser = XMLParser(target=target)
        user = self.user
        if (test_xml is not None) and ("/redacted/" in test_xml):
            user = "redacted"
        path = "/trashbin/{}/trash".format(user)
        full_path = self.webdav_hostname_and_route + path
        if test_xml is None:
            # This is not a test. Download the data.
            # hostname = self.webdav_hostname_and_route
            # password = self.password

            # path = "/trash"
            # results = self.client.execute_request("list", path) # list is not supported

            # ^ server says: Method 'list' is not supported for https://birdo.dyndns.org/nextcloud
            # results = self.client.execute_request("list", path)
            print("* accessing {}".format(path))

            res = self.client.execute_request("list", path)
            # raises webdav3.exceptions.RemoteResourceNotFound if path is wrong
            # print("results: {}".format(res)) # Just says something like "<Response [200]>"
            # print(dir(res))
            '''
            ^ non-hidden members are: 'apparent_encoding', 'close',
            'connection', 'content', 'cookies', 'elapsed', 'encoding',
            'headers', 'history', is_permanent_redirect, 'is_redirect',
            'iter_content', 'iter_lines', 'json', 'links', 'next', 'ok',
            'raise_for_status', 'raw', 'reason', 'request', 'status_code',
            'text', 'url'
            '''
            print("status_code: {}".format(res.status_code)) # 200 no matter what if not a webdav folder, so make sure that's right
            # print("content: {}".format(res.content)) # blank bytestring
            # print("json: {}".format(res.json)) # "<bound method Response.json of <Response [200]>>"
            # print("json: {}".format(res.json())) # "<bound method Response.json of <Response [200]>>"
            # ^ blank apparently ("json.decoder.JSONDecodeError: Expecting value: line 1 column 1 (char 0)")
            # print("text: {}".format(res.text))  # blank
            if len(res.text) < 1:
                return None

            # results_json = res.json()
            # print("json: {}".format(results_json))
            # ^ always raises json.decoder.JSONDecodeError since it is XML not json.
            # So see <https://docs.python.org/3/library/xml.etree.elementtree.html>:
            # root = ET.fromstring(res.text)
            # ^ seems to get a bunch of dumb empty "{DAV}:{}" tags, so use mine:
            parser.feed(res.text)
        else:
            # root = ET.fromstring(example_trash)

            # parser = DAVXMLParser()
            print("feeding text_xml...")
            # parser.feed(test_xml)
            # parser.close()
            # ^ just says CLOSE
            #   (if is subclass of xml.etree.ElementTree.XMLParser)

            # So see <https://docs.python.org/3/library/xml.etree.elementtree.html#xmlparser-objects>:
            parser.feed(test_xml)
        parser.close()
        root = target.davroot
        # Example output: See example_trash global
        # for k, v in root.items(): # 0
        #     print("{}={}".format(k, v))
        # ^ has 0
        print(root)  # <Element '{DAV:}multistatus' at 0x7f2bcb9cf9f0>
        # responses = root.find("response")
        # print("responses={}".format(responses)) # None for d:response, d, DAV:response, response

        for child in root.children:
            # print(child.tag, child.attrib)
            # ^ just shows 3 instances of "{DAV:}response {}"
            print("tag={}".format(child.tag)) # "{DAV:}response"
            # print("attrib={}".format(child.attrib))  # "{}"
            # print("d:href={}".format(child.get("d:href")))  # None
            # print("href={}".format(child.get("href")))  # None
            # print("d={}".format(child.get("d")))  # None
            # print("d:href={}".format(child.get_data("d:href")))
            # For the format of target, see test-list-trash--via+xml-formatter.out
            # for k, v in child.tag.items(): # str has no attribute items
            #     print("    tag.{}={}".format(k, v))
            # print("keys={}".format(child.keys()))  # "[]"
            # print("keys={}".format(child.attrib.keys())) dict_keys([])
            # print("child.attrib('d:href')={}".format(child.attrib.get('d:href')))
            for gc in child.children:
                echo1("  tag={}".format(gc.tag))
                # print("    d:href={}".format(gc.get("d:href")))
                # ^ "<__main__.DAVNode object at 0x7f82d62709a0>"
                href_url_encoded = gc.get_data("d:href")
                echo1("    d:href={}".format(href_url_encoded))
                # ^ such as
                # /nextcloud/remote.php/dav/trashbin/redacted/trash/Blender%202.81%20project.blend1.d1614292530
                # - where "/remote.php/dav" is self.api_route
                rel_url_encoded = self.get_rel_from_partial_url(href_url_encoded)
                if rel_url_encoded is None:
                    # error was already shown above
                    continue
                echo1("    rel_url_encoded={}".format(rel_url_encoded))

                for ggc in gc.children:
                    # print("    tag={}".format(ggc.tag))
                    # ^ len(gc.children)==3 -> d:href, d:propstat, d:propstat
                    if ggc.tag != "d:propstat":
                        continue
                        # then it is d:href
                    prop = ggc.get("d:prop")
                    status_data = ggc.get_data("d:status")
                    echo1("      status_data={}".format(status_data))
                    echo1("      prop:{}".format(prop))  # None if it is d:href and not one of the d:propstat children
                    if prop.get('d:getcontenttype') is not None:
                        if not status_data == "HTTP/1.1 200 OK":
                            if get_verbosity() < 1:
                                echo0("      status_data={}".format(status_data))
                            echo0("        status_data={}".format(status_data))
                            echo0("        getlastmodified={}".format(prop.get_data('d:getlastmodified')))
                            # ^ such as "Sun, 08 Aug 2021 06:33:10 GMT"
                            echo0("        getcontentlength={}".format(prop.get_data('d:getcontentlength')))
                            # ^ getcontentlength is in bytes
                            # print("        resourcetype={}".format(prop.get_data('d:resourcetype')))
                            # ^ resourcetype is self-closing at least in known cases for some reason
                            echo0("        getetag={}".format(prop.get_data('d:getetag')))
                            # ^ getetag is an unknown log integer
                            echo0("        getcontenttype={}".format(prop.get_data('d:getcontenttype')))
                        if results is None:
                            results = []
                        results.append(href_url_encoded)
                        # ^ application/octet-stream
                    elif prop.get('d:quota-used-bytes') is not None:
                        # if status_data == "HTTP/1.1 404 Not Found":
                        # normal if quotas are off (happens in Nextcloud 19.0.5
                        # prop members are (self-closing at least in this case):
                        # - d:quota-used-bytes
                        # - d:quota-available-bytes
                        pass
                    elif (full_path + "/").endswith(href_url_encoded):
                        # If the href is like
                        #   /nextcloud/remote.php/dav/trashbin/redacted/trash/
                        #   then this node is the overall status node:
                        '''
                        <d:response>
                            <d:href>/nextcloud/remote.php/dav/trashbin/owner/trash/</d:href>
                            <d:propstat>
                                <d:prop>
                                    <d:resourcetype>
                                        <d:collection/>
                                    </d:resourcetype>
                                </d:prop>
                                <d:status>HTTP/1.1 200 OK</d:status>
                            </d:propstat>
                        </d:response>
                        '''
                        if status_data != "HTTP/1.1 200 OK":
                            echo0('Error: status for {} is "{}"'
                                  ''.format(href_url_encoded, status_data))
                            return None
                        else:
                            echo0('INFO: status of {} is "{}"'.format(href_url_encoded, status_data))
                    else:
                        # unknown type
                        child_tags = [tagObj.tag for tagObj in prop.children]
                        echo0("Unknown prop type with: {}".format(child_tags))
                        echo0("  href_url_encoded={}".format(href_url_encoded))
                        echo0("  full_path={}".format(full_path))


                    # for gggc in ggc.children:
                    #     len(ggc.children)==2 -> d:prop, d:status
                    #     print("      tag={}".format(gggc.tag))

            # print("text={}".format(child.text))
            #^ blank

            # print(dir(child))
            child_doc = '''
            'append', 'attrib', 'clear', 'extend', 'find', 'findall',
            'findtext', 'get', 'insert', 'items', 'iter', 'iterfind',
            'itertext', 'keys', 'makeelement', 'remove', 'set', 'tag',
            'tail', 'text'
            '''
            # print(child.items) # "<built-in method items of xml.etree.ElementTree.Element object at 0x7ff9131459f0>"
            # for k, v in child.items():
            #     print("    {}={}".format(k, v))
            # ^ has 0
            # for k, v in child.attrib.items():
            #     print("    {}={}".format(k, v))
            # ^ has 0
            # for k, v in child.items():
             #    print("    {}={}".format(k, v))
            # ^ has 0
            # print("    {}={}".format(k, v))
        # responses = list(root.iter("d"))
        # for response in responses:
        #     print("response: {}".format(response))
        # ^ has 0 whether d, d:, d:response, DAV, DAV:, or DAV:response
        # responses = list(root.iter("d"))
        # for response in responses:
        #     print("response: {}".format(response))

        # for response in root.findall('d:response'):
            # print(child.tag, child.attrib)
            # ^ just shows 3 instances of "{DAV:}response {}"
            # for response in root.findall('d'):
            # href = child.get('d:href')
            # print(href)
        return results




class PyNCClientMgr:
    '''
    Access a Nextcloud server using the pyncclient project (the
    nextcloud_client module) which uses the requests package.
    '''
    def __init__(self):
        import nextcloud_client
        # ^ nextcloud_client is the module name for the pyncclient project
        hostname = options.get('webdav_hostname')
        user = options.get('webdav_login')
        password = options.get('webdav_password')
        print("* connecting to {}".format(hostname))
        self.nc = nextcloud_client.Client(hostname)
        self.nc.login(user, password)

    def get_trash(self):
        user = options.get('webdav_login')
        path = "trash" # 404
        path = "/trash" # 404
        # path = "/trashbin/{}/trash".format(user)  # 404
        path = "trashbin/{}/trash".format(user)  # 404
        results = None
        '''
        import nextcloud_client
        init_path = nextcloud_client.__file__
        dir_path = os.path.dirname(init_path)
        sub_path = os.path.join(dir_path, "nextcloud_client.py")
        raise NotImplementedError(
            'get_trash isn\'t programmed yet. To help, see "{}",'
            ' <https://github.com/pragmaticindustries/pyncclient> or'
            ' <https://pypi.org/project/pyncclient/>'.format(sub_path)
        )
        '''
        print("* accessing {}".format(path))
        results = self.nc.list(path, depth=1, properties=None)

        return results

    def upload(self, path):
        raise NotImplementedError("upload")
        # nc.mkdir('testdir')
        # nc.put_file('testdir/remotefile.txt', 'localfile.txt')

    def share(self, path):
        raise NotImplementedError("share")
        # link_info = nc.share_file_with_link('testdir/remotefile.txt')
        print("Here is your link: " + link_info.get_link())


def main():
    global options
    if options is None:
        options = {}
    changed = False
    booleans = ['scrub-scribus']
    more_options = {}
    var_name = None
    for argI in range(1, len(sys.argv)):
        arg = sys.argv[argI]
        if var_name is not None:
            more_options[var_name] = arg
            var_name = None
        elif arg.startswith("--"):
            var_name = arg[2:]
            if arg == "--verbose":
                set_verbosity(1)
            elif arg == "--debug":
                set_verbosity(2)
            elif arg == "--scrub-scribus":
                op = var_name
            if var_name in booleans:
                more_options[var_name] = True
                echo0("{}=True".format(var_name))
                var_name = None
    for k, v in DEFAULT_OPTIONS.items():
        current_v = options.get(k)
        if (current_v is None) or (len(current_v.strip()) == 0):
            answer = input(k + OPTIONS_HELP[k]+ ": ")
            # TODO: ^ hide webdav_password while typing
            options[k] = answer
            changed = True

    for k, v in options.items():
        if (v is None) or (len(v.strip()) == 0):
            raise ValueError("No options can be blank: {}".format(options))

    if changed:
        save_options()
    # mgr = PyNCClientMgr()  # always has 404 on trash URLs (see PyNCClientMgr's own get_trash)
    mgr = WebDav3Mgr()
    results = mgr.get_trash()
    if results is None:
        echo0("There were no results.")
        return 1
    if len(more_options) < 1:
        usage()
    echo0("Checking {} result(s)...".format(len(results)))
    for result in results:
        slashI = result.rfind("/")
        name = result
        if slashI > -1:
            name = result[slashI+1:]
        echo1("  - "+name)
        if more_options.get("scrub-scribus") is True:
            is_match = False
            for pattern in SCRIBUS_AUTOSAVES:
                match = re.search(pattern, name)
                # It is either None or something like
                #   <re.Match object; span=(0, 70), match='The%20Path%20of%20Resistance_autosave_08_08_2021_>
                echo2("    - match vs {}...{}".format(pattern, match))
                if match:
                    # is object rather than None
                    is_match = True
                    break
            if is_match:
                mgr.delete(result)
    echo0("Done")

    return 0





if __name__ == "__main__":
    sys.exit(main())

