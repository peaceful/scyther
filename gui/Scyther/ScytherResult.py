"""
	Scyther : An automatic verifier for security protocols.
	Copyright (C) 2007-2013 Cas Cremers

	This program is free software; you can redistribute it and/or
	modify it under the terms of the GNU General Public License
	as published by the Free Software Foundation; either version 2
	of the License, or (at your option) any later version.

	This program is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with this program; if not, write to the Free Software
	Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
"""

#
# Scyther Result
#

class ScytherResult(object):
    def isBool(self):
        return False

class ScytherResultBool(ScytherResult):
    def __init__(self,b):
        self.value = b

    def result(self):
        return self.value

    def isBool(self):
        return True

    def merge(self,other):
        assert(isinstance(other,ScytherResultBool))
        self.value = self.value and other.value

class ScytherResultTuple(ScytherResult):
    def __init__(self,(output,claims,errors,warnings)):
        self.output = output
        self.claims = claims
        self.errors = errors
        self.warnings = warnings

    def merge(self,other):
        if other == None:
            # Allow mergine with none for bootstrapping sequence merges
            return
        assert(isinstance(other,ScytherResultTuple))
        self.output = mergeOutputs(self.output,other.output)
        self.claims = mergeClaims(self.claims,other.claims)
        self.errors = mergeLines(self.errors,other.errors)
        self.warnings = mergeLines(self.warnings,other.warnings)

def makeScytherResult(rv):
    if isinstance(rv,bool):
        return ScytherResultBool(rv)
    else:
        return ScytherResultTuple(rv)

#---------------------------------------------------------------------------

def findPrefix(o,prefix):
    for (i,l) in enumerate(o):
        if l.startswith(prefix):
            return i
    return -1

def cleverCombine(l1,l2,i):
    if "At least" in l1:
        return l1
    if "within bounds" in l2:
        return l1
    return l2

def revertSplit(ll):
    res = ""
    for l in ll:
        res += l + "\n"
    return res

def mergeOutputs(o1,o2):
    res = o1.splitlines()
    for l in o2.splitlines():
        if l not in res:
            if l.startswith("claim"):
                i = l.find(":")
                if i >= 0:
                    n = findPrefix(res,l[:i+1])
                    if n >= 0:
                        res[n] = cleverCombine(res[n],l,i)
                        continue
            res.append(l)
    return revertSplit(res)

def mergeClaims(l1,l2=[]):
    if l1 == None:
        l1 = []
    if l2 == None:
        l2 = []
    
    allclaims = l1 + l2
    if len(allclaims) == 0:
        return None

    res = []
    for cl in allclaims:
        merged = False
        for clx in res:
            if clx.merge(cl):
                merged = True
                break
        if not merged:
            res.append(cl)
    return res

def mergeLines(l1,l2):
    res = l1[:]
    for ll in l2:
        if ll not in res:
            res.append(ll)
    return res

#---------------------------------------------------------------------------

# vim: set ts=4 sw=4 et list lcs=tab\:>-:
