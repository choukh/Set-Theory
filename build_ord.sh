#!/bin/sh

echo "building Natural"
coqc -R . ZFC lib/Natural.v

echo "building EST7_2"
coqc -R . ZFC EST7_2.v
echo "building EX7_1"
coqc -R . ZFC EX7_1.v
