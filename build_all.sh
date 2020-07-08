#!/bin/sh

echo "building TG0"
coqc -R . ZFC TG0.v
echo "building TG1"
coqc -R . ZFC TG1.v
echo "building TG2"
coqc -R . ZFC TG2.v
echo "building TG3"
coqc -R . ZFC TG3.v
echo "building TG4"
coqc -R . ZFC TG4.v
coqc -R . ZFC TG_full.v
echo "building EST2"
coqc -R . ZFC EST2.v
echo "building CH2"
coqc -R . ZFC CH2.v
echo "building EST3_1"
coqc -R . ZFC EST3_1.v
echo "building EST3_2"
coqc -R . ZFC EST3_2.v
echo "building EST3_3"
coqc -R . ZFC EST3_3.v
echo "building CH3_1"
coqc -R . ZFC CH3_1.v
echo "building CH3_2"
coqc -R . ZFC CH3_2.v
echo "building EST4_1"
coqc -R . ZFC EST4_1.v
echo "building EST4_2"
coqc -R . ZFC EST4_2.v
echo "building EST4_3"
coqc -R . ZFC EST4_3.v
echo "building CH4"
coqc -R . ZFC CH4.v
echo "building EST5_1"
coqc -R . ZFC EST5_1.v
echo "building EST5_2"
coqc -R . ZFC EST5_2.v
echo "building EST5_3"
coqc -R . ZFC EST5_3.v
echo "building EST5_4"
coqc -R . ZFC EST5_4.v
echo "building CH5_1"
coqc -R . ZFC CH5_1.v