#!/bin/sh

echo "building ZFC0"
coqc -R . ZFC ZFC0.v
echo "building ZFC1"
coqc -R . ZFC ZFC1.v
echo "building ZFC2"
coqc -R . ZFC ZFC2.v
echo "building ZFC3"
coqc -R . ZFC ZFC3.v
echo "building Essential"
coqc -R . ZFC lib/Essential.v

echo "building EST2"
coqc -R . ZFC EST2.v
echo "building EX2"
coqc -R . ZFC EX2.v
echo "building EST3_1"
coqc -R . ZFC EST3_1.v
echo "building EST3_2"
coqc -R . ZFC EST3_2.v
echo "building EST3_3"
coqc -R . ZFC EST3_3.v
echo "building EX3_1"
coqc -R . ZFC EX3_1.v
echo "building EX3_2"
coqc -R . ZFC EX3_2.v
echo "building EST7_1"
coqc -R . ZFC EST7_1.v
echo "building Relation"
coqc -R . ZFC lib/Relation.v
echo "building FuncFacts"
coqc -R . ZFC lib/FuncFacts.v

echo "building EST4_1"
coqc -R . ZFC EST4_1.v
echo "building EST4_2"
coqc -R . ZFC EST4_2.v
echo "building EST4_3"
coqc -R . ZFC EST4_3.v
echo "building EX4"
coqc -R . ZFC EX4.v
echo "building Natural"
coqc -R . ZFC lib/Natural.v
