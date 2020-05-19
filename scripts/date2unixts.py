#!/usr/bin/env python3
# Convert every line's text before "|" from ISO date to Unix timestamp.

# We naively assume all dates are in UTC, which isn't quite right, but we
# don't have timezones nor time-of-day information, and we only really
# care about the day anyway. As long as we do it consistently we're fine.

# So Python2 and Python3 both work
from __future__ import print_function

import datetime
import sys

for line in sys.stdin:
    text_date, rest = line.split('|',1)
    ts_date = datetime.datetime.strptime(text_date, "%Y-%m-%d")
    ts_number = ts_date.strftime('%s')
    rest = rest.rstrip()
    print(ts_number, '|', rest, sep='')
