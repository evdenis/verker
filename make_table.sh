#!/bin/bash

./process_report.pl csv/aggregate_data.csv &&
pdflatex table.tex &&
okular table.pdf
