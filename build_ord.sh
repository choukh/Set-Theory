#!/bin/sh

echo "building EST7_1"
coqc -R . ZFC EST7_1.v
echo "building PartialOrder"
coqc -R . ZFC lib/PartialOrder.v
echo "building EST7_2"
coqc -R . ZFC EST7_2.v
echo "building EX7_1"
coqc -R . ZFC EX7_1.v
