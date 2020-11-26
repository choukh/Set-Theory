#!/bin/sh

echo "building FuncFacts"
coqc -R . ZFC lib/FuncFacts.v
echo "building Natural"
coqc -R . ZFC lib/Natural.v

echo "building EST5_1"
coqc -R . ZFC EST5_1.v
echo "building EST5_2"
coqc -R . ZFC EST5_2.v
echo "building EST5_3"
coqc -R . ZFC EST5_3.v
echo "building EST5_4"
coqc -R . ZFC EST5_4.v
echo "building EX5"
coqc -R . ZFC EX5.v
echo "building EST5_5"
coqc -R . ZFC EST5_5.v
echo "building EST5_6"
coqc -R . ZFC EST5_6.v
echo "building EST5_7"
coqc -R . ZFC EST5_7.v
echo "building Real"
coqc -R . ZFC lib/Real.v
