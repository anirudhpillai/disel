#!/usr/bin/env python3

import subprocess
import re
import time


proposer1 = "(./PaxosMain.d.byte -me 1 -mode proposer 1 127.0.0.1 8000 2 127.0.0.1 8001 3 127.0.0.1 8002 4 127.0.0.1 8003 5 127.0.0.1 8004 &) > proposer1.log 2>&1"
proposer2 = "(./PaxosMain.d.byte -me 2 -mode proposer 1 127.0.0.1 8000 2 127.0.0.1 8001 3 127.0.0.1 8002 4 127.0.0.1 8003 5 127.0.0.1 8004 &) > proposer2.log 2>&1"
acceptor1 = "(./PaxosMain.d.byte -me 3 -mode acceptor 1 127.0.0.1 8000 2 127.0.0.1 8001 3 127.0.0.1 8002 4 127.0.0.1 8003 5 127.0.0.1 8004 &) > acceptor1.log 2>&1"
acceptor2 = "(./PaxosMain.d.byte -me 4 -mode acceptor 1 127.0.0.1 8000 2 127.0.0.1 8001 3 127.0.0.1 8002 4 127.0.0.1 8003 5 127.0.0.1 8004 &) > acceptor2.log 2>&1"
acceptor3 = "(./PaxosMain.d.byte -me 5 -mode acceptor 1 127.0.0.1 8000 2 127.0.0.1 8001 3 127.0.0.1 8002 4 127.0.0.1 8003 5 127.0.0.1 8004 &) > acceptor3.log 2>&1"

a1 = subprocess.Popen(acceptor1, shell=True)
a2 = subprocess.Popen(acceptor2, shell=True)
a3 = subprocess.Popen(acceptor3, shell=True)
p1 = subprocess.Popen(proposer1, shell=True)
p2 = subprocess.Popen(proposer2, shell=True)

consensus_achieved = True
consensus_value = None

exit_codes = [p.wait() for p in [a1, a2, a3]]
print(exit_codes)

time.sleep(2)
for i in range(1, 4):
    line = subprocess.check_output(['tail', '-1', "acceptor{0}.log".format(i)])
    line = line.decode("utf-8")
    print(line)

    pattern = r"got msg in protocol (\d) with tag = (\d), contents = \[(\d); (\d)\]"
    match = re.match(pattern, line)

    if not match or (consensus_value and consensus_value != match.group(4)):
        print("Error in acceptor %d" % i)
        consensus_achieved = False
        break
    else:
        # print("Acceptor %d accepted %s" % (i, match.group(4)))
        consensus_value = match.group(4)

print("\n")
print("=" * 20)

if consensus_achieved:
    print("\nConsesus achieved on value: %s" % consensus_value)
else:
    print("\nConsesus not achieved")
