#!/bin/sh

echo "building EST6_1"
coqc -R . ZFC EST6_1.v
echo "building EST6_2"
coqc -R . ZFC EST6_2.v
echo "building EST6_3"
coqc -R . ZFC EST6_3.v
echo "building CH6"
coqc -R . ZFC CH6.v
