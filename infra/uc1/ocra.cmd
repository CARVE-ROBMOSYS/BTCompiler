set on_failure_script_quits;
set ocra_discrete_time;
ocra_check_consistency -i ./system.oss;
reset;
#ocra_check_implementation -i ./system.oss -I ./system.smv -c BT_FSM;
#reset;
ocra_check_refinement -i ./system.oss;
#reset;
#ocra_check_composite_impl -i ./system.oss -m ./system.map -M -s out.smv;
quit;
