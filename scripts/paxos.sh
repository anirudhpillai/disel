#!/usr/bin/env bash

if ! [ -x ./PaxosMain.d.byte ]
then
    echo 'PaxosMain.d.byte not found!'
    echo 'Run `make PaxosMain.d.byte` first.'
    exit 1
fi

(./PaxosMain.d.byte -me 1 -mode acceptor 0 127.0.0.1 8000 1 127.0.0.1 8001 2 127.0.0.1 8002 3 127.0.0.1 8003 &) >acceptor1.log

(./PaxosMain.d.byte -me 2 -mode acceptor 0 127.0.0.1 8000 1 127.0.0.1 8001 2 127.0.0.1 8002 3 127.0.0.1 8003 &) >acceptor2.log

(./PaxosMain.d.byte -me 3 -mode acceptor 0 127.0.0.1 8000 1 127.0.0.1 8001 2 127.0.0.1 8002 3 127.0.0.1 8003 &) >acceptor3.log

./PaxosMain.d.byte -me 0 -mode proposer 0 127.0.0.1 8000 1 127.0.0.1 8001 2 127.0.0.1 8002 3 127.0.0.1 8003 | tee proposer.log
