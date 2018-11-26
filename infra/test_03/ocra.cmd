set on_failure_script_quits;
set ocra_discrete_time;
ocra_check_consistency -i ./system.oss;
reset;
# Implementation check fails because the component contract assumptions are too weak.
#ocra_check_implementation -i ./system.oss -I ./comp_spec.smv -c comp_spec;
#reset;
ocra_check_refinement -i ./system.oss;
reset;
ocra_check_composite_impl -i ./system.oss -m ./system.map -M -s out.smv;
quit;
