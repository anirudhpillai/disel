#!/usr/bin/env bash

if ! [ -x ./PaxosMain.d.byte ]
then
    echo 'PaxosMain.d.byte not found!'
    echo 'Run `make PaxosMain.d.byte` first.'
    exit 1
fi

(./PaxosMain.d.byte -me 3 -mode acceptor 1 127.0.0.1 8000 2 127.0.0.1 8001 3 127.0.0.1 8002 4 127.0.0.1 8003 5 127.0.0.1 8004 &) > acceptor1.log 2>&1

(./PaxosMain.d.byte -me 4 -mode acceptor 1 127.0.0.1 8000 2 127.0.0.1 8001 3 127.0.0.1 8002 4 127.0.0.1 8003 5 127.0.0.1 8004 &) > acceptor2.log 2>&1

(./PaxosMain.d.byte -me 5 -mode acceptor 1 127.0.0.1 8000 2 127.0.0.1 8001 3 127.0.0.1 8002 4 127.0.0.1 8003 5 127.0.0.1 8004 &) > acceptor3.log 2>&1

(./PaxosMain.d.byte -me 1 -mode proposer 1 127.0.0.1 8000 2 127.0.0.1 8001 3 127.0.0.1 8002 4 127.0.0.1 8003 5 127.0.0.1 8004 &) > proposer1.log 2>&1

./PaxosMain.d.byte -me 2 -mode proposer 1 127.0.0.1 8000 2 127.0.0.1 8001 3 127.0.0.1 8002 4 127.0.0.1 8003 5 127.0.0.1 8004 | tee proposer2.log
