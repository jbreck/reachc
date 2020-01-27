import choraconfig, glob, os.path

batch = choraconfig.get_default_batch_dict()

#chc-comp19/lia-lin
#batch["root"] = os.path.join(choraconfig.get_tool_root("cfind"), "experiments/benchmarks/small/")
batch["root"] = os.path.join(choraconfig.get_tool_root("cfind"), "experiments/benchmarks/spacer_subset/")
#batch["files"] = ( glob.glob(batch["root"] + "lia-lin/*.smt2") + glob.glob(batch["root"] + "lia-nonlin/*.smt2") )
batch["files"] = ( glob.glob(batch["root"] + "lia-lin/*.smt2") )
batch["format_style"] = "assert"
batch["toolIDs"] = ["cfind","spacer471"]
#batch["format_col_width_proportional"] = True
batch["timeout"] = 60

