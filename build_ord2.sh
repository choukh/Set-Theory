#!/bin/sh

echo "building Class"
coqc -R . ZFC lib/Class.v
echo "building LoStruct"
coqc -R . ZFC lib/LoStruct.v
echo "building EST8_1"
coqc -R . ZFC EST8_1.v
echo "building EST8_2"
coqc -R . ZFC EST8_2.v
echo "building EST8_3"
coqc -R . ZFC EST8_3.v
echo "building EST8_4"
coqc -R . ZFC EST8_4.v
echo "building EX8_1"
coqc -R . ZFC EX8_1.v
echo "building EX8_2"
coqc -R . ZFC EX8_2.v
