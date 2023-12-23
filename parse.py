import sys
from delphin import ace

response = ace.parse("erg-2018-x86-64-0.9.34.dat",sys.argv[1])
ret = response.result(0)

from delphin.codecs import mrsprolog

m = ret.mrs()

print(mrsprolog.encode(m))
