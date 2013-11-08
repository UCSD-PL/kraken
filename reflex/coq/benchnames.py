#!/usr/bin/env python2.7

import sys

input = sys.stdin.read()

try:
  sys.stdout.write(
{
'AirbagImmAfterCrash'     : 'Airbags are deployed immediately after crash',
'CrashDisablesLock'       : 'Doors do not lock after crash',
'CrashEnablesAirbag'      : 'Airbags only deploy if there has been a crash',
'CruiseOffImmAfterBrakes' : 'Cruise control turns off immediately after braking',
'CarNonInterference'      : 'Components do not interfere with the engine',
'QuarkNonInterference'    : 'Different domains do not interfere',
'UnlockImmAfterAirbag'    : 'Doors unlock immediately after the airbags are deployed',
'CProcUnique'             : 'Cookie processes are unique per domain',
'CookieSameDomain'        : 'Cookies may only be forwarded to the cookie process of the proper domain',
'CounterObeyed'           : 'Login attempts are preceeded by approval from counter component',
'LoginAtt0'               : 'The first attempt to login disables itself',
'LoginAtt1'               : 'The second attempt to login disables itself',
'LoginAtt2'               : 'The third attempt to login disables all attempts',
'LoginAttEnables'         : 'Each login attempt enables the next one',
'LoginEnablesPTY'         : 'A succesful login enables the pseudo-terminal creation',
'AccessCorrectDisk'       : 'Kernel only sends a file where the disk indicates',
'AccessCorrect'           : 'Files are only requested after authorization',
'AuthCorrect'             : 'A client is only spawned on successful login',
'AuthEnablesReq'          : 'Files can only be requested after login',
'NoDupClients'            : 'Clients are never duplicated',
}[input]
  )
except KeyError:
  sys.stdout.write(input)

