#!/bin/bash

java -Xms16g -Xmx24g -jar tla2tools.jar -workers 16 -config raft.cfg raft.tla

