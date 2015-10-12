#!/usr/bin/env python

# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


import sys
import re

filename = sys.argv[1]
comment = sys.argv[2]

notice = """%s Copyright 2015 Heidelberg University Copyright and related rights are
%s licensed under the Solderpad Hardware License, Version 0.51 (the "License");
%s you may not use this file except in compliance with the License. You may obtain
%s a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
%s required by applicable law or agreed to in writing, software, hardware and
%s materials distributed under this License is distributed on an "AS IS" BASIS,
%s WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
%s the License for the specific language governing permissions and limitations
%s under the License.
""" % (comment, comment,comment, comment, comment, comment, comment, comment, comment)

use_m4_pattern = re.compile(r'/\* _use_m4_([^*]|[\r\n]|(\*+([^*/]|[\r\n])))*\*+/')
notice_pattern = re.compile(r'// Copyright 2015 Heidelberg(.*)under the License\.', re.DOTALL)

with open(filename, 'r') as f:
    orig = f.read()

    found_notice = notice_pattern.search(orig)
    if not found_notice:
        with open(filename, 'w') as f2:
            found_m4 = use_m4_pattern.search(orig)
            if found_m4:
                #print "found m4: ", found_m4.group(0)
                f2.write(found_m4.group(0))
                f2.write('\n\n' + notice + '\n\n')
                f2.write(use_m4_pattern.sub('', orig))
                print "Prepended '%s' with copyright notice using M4 magic string." % (filename)
            else:
                f2.write(notice + '\n\n' + orig)
                print "Prepended '%s' with copyright notice." % (filename)

