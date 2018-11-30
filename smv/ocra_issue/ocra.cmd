# This document contains no USA or EU export controlled technical data.

set on_failure_script_quits;
set ocra_discrete_time;
ocra_check_consistency -i ./system.oss;
reset;
ocra_check_composite_impl -i ./system.oss -m ./system.map -M -s out.smv;
quit;
