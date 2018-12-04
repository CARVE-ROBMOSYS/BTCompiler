set on_failure_script_quits;
set ocra_discrete_time;
ocra_check_consistency -i ./system.oss;
#reset;
reset;
ocra_check_refinement -i ./system.oss;
reset;
#ocra_print_implementation_template -i ./system.oss -m ./system.map
#ocra_check_composite_impl -i ./system.oss -m ./system.map -M -s out.smv;
#ocra_check_implementation -i ./system.oss -I ./bt.smv -c bt_spec;
quit;
