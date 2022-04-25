import angr
from mimetypes import init
from tracemalloc import start


import argparse
from angrutils import plot_cfg, hook0, set_plot_style
import bingraphvis
import filecmp
import os
import subprocess
import networkx as nx
from sqlalchemy import intersect
from sympy import intersection
from stmtInfo import stmtInfo

class Info(object):
    def __init__(self):
        self.args = None

        self.binaryfile =None
        self.asmfile = None
        self.picflag = None

        self.project = None
        self.cfg = None
        self.nodes_list = None
        self.tempVar = dict()

        self.bb_info = dict()
        self.bb_info_new = dict()        
        
        self.regs = dict()
        self.mem = dict()
        self.storeIns = set()
        self.func = None
		
        self.esp = 24
        self.ebp = 28
        self.debug = False
        self.ebp_stack = list()
        self.backedge_in = set()
        self.isChanged = True
        self.curr_func = 0
        self.curr_asm_ins = None
        self.storeInsns_map = dict()

global p
p = Info()

def op_data(operator,d1=None,d2=None,d3=None,d4=None):
	
	if(operator == 'Iop_Add32'):
		return d1 + d2

def check(flag1,flag2):
	if flag1 and flag2 :
		return True
	else:
		return False
		
def parse_data(expr, blockAddr, tempVar_map):

	flag = False
	val = set()
	
	#print(expr.tag,expr)
	if expr.tag == "Iex_Const" :
		flag=True
		
		val.add(expr.con.value)
			
	if expr.tag == 'Iex_RdTmp' :
		if expr.tmp in tempVar_map :
			flag=True
			val = tempVar_map[expr.tmp]
	if expr.tag == 'Iex_Get' :
		if expr.offset in p.bb_info[blockAddr]['regs'] :
			flag = True 
			val = p.bb_info[blockAddr]['regs'][expr.offset]
			#p.regs[expr.offset] 
		else :
			print("at " + hex(p.curr_asm_ins))
			print("loading from uninitialized register")	
	if expr.tag == 'Iex_Load' :
		flag1,addr_set = parse_data(expr.addr, blockAddr, tempVar_map)	
		if flag1 :
			flag = True
			# print("\nIN LOAD :")
			# print(p.storeInsns_map[nodeAddr])
			# print(str(hex(addr)))
			for addr in addr_set:
				if (addr) not in p.storeInsns_map[blockAddr] :
					#print("Loading addr : " + str(hex(addr)))
					if(int(addr)==0):
						return (flag1,val)
					else :
						loading_offset_addr = 0x100000000-int(addr)
					print("at " + hex(p.curr_asm_ins))
					print("ebp = esp "+str(p.bb_info[blockAddr]['regs'][28]))
					print("Use of Uninitialized Mem loc at esp - " + str(hex(loading_offset_addr)))
				else :
					val=(p.bb_info[blockAddr]['mem'][addr])
							
		
	if expr.tag == 'Iex_Binop' :
		flag1,data1 = parse_data(expr.args[0], blockAddr, tempVar_map)
		flag2,data2 = parse_data(expr.args[1], blockAddr, tempVar_map)
		op = expr.op
		#print(op)
		if(op == 'Iop_Add32' and check(flag1,flag2) ):
			flag = True
			
			for d1 in data1 :
				for d2 in data2:
					val.add(d1+d2)
			#val = data1+data2
		if(op == 'Iop_Sub32' and check(flag1,flag2)) :
			
			flag = True
		
			for d1 in data1 :
				for d2 in data2:
					#print(d1,d2)
					val.add(d1-d2)
					#print(val)
			#val = data1-data2
		if(op =='Iop_And32' and check(flag1,flag2)) :
			flag=True

			for d1 in data1 :
				for d2 in data2:
					val.add(d1&d2)
			#val = data1 & data2
		if(op =='Iop_CmpEQ32' and check(flag1,flag2)) :
			flag=True
			
			for d1 in data1 :
				for d2 in data2:

					val.add(d1==d2)
			#val = data1 == data2
		if(op =='Iop_CmpNE32' and check(flag1,flag2)) :
			flag=True
		
			for d1 in data1 :
				for d2 in data2:
					val.add(d1!=d2)
			#val = data1 != data2
		if(op =='Iop_CmpLE32S' and check(flag1,flag2)) :
			
			flag=True
	
			for d1 in data1 :
				for d2 in data2:
					val.add(d1<=d2)
			#val = data1 <= data2
		if(op =='Iop_CmpLE32U' and check(flag1,flag2)) :
			
			flag=True
			
			for d1 in data1 :
				for d2 in data2:
					val.add(d1<=d2)
			#val = data1 <= data2
		if(op =='Iop_CmpLT32S' and check(flag1,flag2)) :
			
			flag=True
			val = set()
			for d1 in data1 :
				for d2 in data2:
					val.add(d1<d2)
			#val = data1 < data2
		if(op =='Iop_CmpLT32U' and check(flag1,flag2)) :
			flag=True

			for d1 in data1 :
				for d2 in data2:
					val.add(d1<d2)
			#val = data1 < data2
		#print(op)
	if expr.tag == 'Iex_Unop' :
		flag1,data1 = parse_data(expr.args[0], blockAddr, tempVar_map)
		op = expr.op
		if(op == 'Iop_1Uto32' and flag1):	
			val = data1
		if(op == 'Iop_1Sto32' and flag1):	
			val = data1

		if(op == 'Iop_8Uto32' and flag1):	
			val = data1

	if(p.debug):	
		print(flag,val)
	return (flag,val)
	
def parse_stmts(stmt, blockAddr, tempVar_map):

	if(p.debug):
		print(stmt.tag,stmt)
	storeIns = p.storeInsns_map[blockAddr]        
	if stmt.tag == 'Ist_IMark' :
		p.curr_asm_ins = stmt.addr        
	if stmt.tag == 'Ist_Put' :
		flag,data = parse_data(stmt.data, blockAddr, tempVar_map)
		#print(flag,data)
		if flag and data != None :
			if stmt.offset not in p.bb_info[blockAddr]['regs'] :
				p.bb_info[blockAddr]['regs'][stmt.offset] = set()

			p.bb_info[blockAddr]['regs'][stmt.offset]=data
			# if stmt.offset == 28 :

			# 	curr_node = None
			# 	for node in p.nodes_list:
			# 		if node.block_id == blockAddr :
			# 			curr_node = node
			# 			break
			# 	print(blockAddr)
			# 	print(hex(p.curr_asm_ins))
			# 	print(curr_node.function_address, p.curr_func)
			# 	print(p.ebp_stack)
			# 	if curr_node.function_address == p.curr_func :
					
			# 		if p.ebp_stack != []:
			# 			val = p.ebp_stack.pop(-1)
			# 			p.bb_info[blockAddr]['regs'][stmt.offset]=val
			# 	else :
			# 		p.ebp_stack.append(p.bb_info[blockAddr]['regs'][stmt.offset])
			# 		p.curr_func = curr_node.function_address
			# 	print(p.ebp_stack)
	
			#p.regs[stmt.offset] = data
		
		# else :
		# 	p.regs[stmt.offset] = data
	if stmt.tag == 'Ist_WrTmp':
		flag,data = parse_data(stmt.data, blockAddr, tempVar_map)
		#print(flag,data)
		if flag and data != None :
			if stmt.tmp not in tempVar_map :
				tempVar_map[stmt.tmp] = set()	
			tempVar_map[stmt.tmp]=data
	if stmt.tag == 'Ist_Store' :
		flag,addr_set = parse_data(stmt.addr, blockAddr, tempVar_map)
		flag1,data_set = parse_data(stmt.data, blockAddr, tempVar_map)
		if flag :
			#print(str(hex(p.curr_asm_ins))+" storing addr : " + str(hex(addr)))
			# print("BEFORE ------")
			# print(storeIns,addr_set)
			storeIns = storeIns.union(addr_set)

			for addr in addr_set:
				if addr not in p.bb_info[blockAddr]['mem'] :
					p.bb_info[blockAddr]['mem'][addr]=set()
				p.bb_info[blockAddr]['mem'][addr]=data_set

			# print("AFTER -----")
			# print(storeIns)
	if(p.debug) : 	
		print(tempVar_map)
		print(p.bb_info[blockAddr]['regs'])
		print(p.bb_info[blockAddr]['mem'])
		print(storeIns)
		print('\n\n') 
	return storeIns   	


def Topo(nodes_list):
	


	#p.curr_func=next_nodes[0].function_address
	in_degree = dict()
	visited = set()

	for i in nodes_list : 
	
		# print(hex(i.addr))
		# print(len(i.predecessors))
		# for temp in i.predecessors :
		# 	print(temp)
		# print("\n")
		#in_degree.append((i.block_id,len(i.predecessors)))
		in_degree[i.block_id] = len(i.predecessors)
		p.storeInsns_map[i.block_id] = set()
		p.bb_info[i.block_id] = dict()
		p.bb_info[i.block_id]['regs'] = dict()
		p.bb_info[i.block_id]['mem'] = dict()

	
	p.bb_info[nodes_list[0].block_id]['regs'][p.ebp]={0}
	p.bb_info[nodes_list[0].block_id]['regs'][p.esp]={0}


	next_nodes = [nodes_list[0]]
	# for blockId in in_degree :
	# 	if in_degree[blockId] == 0:
	# 		for node in nodes_list:
	# 			if node.block_id == blockId :
	# 				next_nodes.append(node)
	# 				break

	try:
		cycles = list(nx.simple_cycles(p.cfg.graph))
	except:
		cycles = []

	# print(cycles)

	while next_nodes :

		node = next_nodes.pop(0)

		print("visiting node - ",hex(node.addr))
		visited.add(node.block_id)

		if len(node.predecessors) > 0 : 

			i = 0
			while i < len(node.predecessors) and node.predecessors[i].block_id not in visited:
				i += 1
			p.storeInsns_map[node.block_id] = p.storeInsns_map[node.predecessors[i].block_id].copy()

			for pre in node.predecessors[i:]:
				if pre.block_id not in visited:
					continue
				p.storeInsns_map[node.block_id] = p.storeInsns_map[node.block_id].intersection(p.storeInsns_map[pre.block_id])
				for r in p.bb_info[pre.block_id]['regs']:
					if r not in p.bb_info[node.block_id]['regs']:
						p.bb_info[node.block_id]['regs'][r]=set()
					p.bb_info[node.block_id]['regs'][r]=p.bb_info[node.block_id]['regs'][r].union(p.bb_info[pre.block_id]['regs'][r])

				for m in p.bb_info[pre.block_id]['mem']:
					if m not in p.bb_info[node.block_id]['mem']:
						p.bb_info[node.block_id]['mem'][m]=set()
					p.bb_info[node.block_id]['mem'][m]=p.bb_info[node.block_id]['mem'][m].union(p.bb_info[pre.block_id]['mem'][m])


			#p.bb_info[node.addr]['regs'] = p.bb_info[node.predecessors[0].addr]['regs'].copy()
			# for pre in node.predecessors:
			
			# 	p.storeInsns_map[node.addr] = p.storeInsns_map[node.addr].intersection(p.storeInsns_map[pre.addr])	
				
		try:
			stmts = node.block.vex.statements
		except:
			stmts = []

		tempVar_map = dict()
		for stmt in stmts :
			l = parse_stmts(stmt, node.block_id, tempVar_map)
			# print("exited ---")
			# print(l)
			for i in l :
				p.storeInsns_map[node.block_id].add(i)
			# print("final ----")
			# print(p.storeInsns_map[node.addr])

		for suc in node.successors : 
			if suc in visited :
				continue
			in_degree[suc.block_id] -= 1

			for suc_pre in suc.predecessors :
				if suc_pre.block_id in visited:
					continue

				flag = False
				for c in cycles :
					if suc in c and suc_pre in c :
						flag = True
						break
				if flag == True :
					in_degree[suc.block_id] -= 1

			if in_degree[suc.block_id] == 0 :
				next_nodes.append(suc)


	return



def traverseGraph(nodes_list):

	# p.isChanged = True

	# for i in nodes_list : 
	
	# 	# print(hex(i.addr))
	# 	# print(len(i.predecessors))
	# 	# for temp in i.predecessors :
	# 	# 	print(temp)
	# 	# print("\n")
	# 	#in_degree.append((i.block_id,len(i.predecessors)))
	# 	p.storeInsns_map[i.block_id] = set()
	# 	p.bb_info[i.block_id] = dict()
	# 	p.bb_info[i.block_id]['regs'] = dict()
	# 	p.bb_info[i.block_id]['mem'] = dict()

	# p.bb_info[nodes_list[0].block_id]['regs'][p.ebp]={0}
	# p.bb_info[nodes_list[0].block_id]['regs'][p.esp]={0}

	# p.bb_info_new = p.bb_info.copy()

	# while(p.isChanged):

	# 	for node in nodes_list :


	# 		if len(node.predecessors) > 0 : 
	# 			p.storeInsns_map[node.block_id] = p.storeInsns_map[node.predecessors[0].block_id].copy()

	# 			# print(hex(node.addr), "no..........." , len(node.predecessors))
	# 			for pre in node.predecessors:
	# 				# print("\n 1 --------")
	# 				# print(p.storeInsns_map[node.addr])
	# 				# print("\n 2 --------")
	# 				# print(p.storeInsns_map[pre.addr])
	# 				p.storeInsns_map[node.block_id] = p.storeInsns_map[node.block_id].intersection(p.storeInsns_map[pre.block_id])
	# 				for r in p.bb_info[pre.block_id]['regs']:
	# 					if r not in p.bb_info[node.block_id]['regs']:
	# 						p.bb_info[node.block_id]['regs'][r]=set()
	# 					p.bb_info[node.block_id]['regs'][r]=p.bb_info[node.block_id]['regs'][r].union(p.bb_info[pre.block_id]['regs'][r])

	# 				for m in p.bb_info[pre.block_id]['mem']:
	# 					if m not in p.bb_info[node.block_id]['mem']:
	# 						p.bb_info[node.block_id]['mem'][m]=set()
	# 					p.bb_info[node.block_id]['mem'][m]=p.bb_info[node.block_id]['mem'][m].union(p.bb_info[pre.block_id]['mem'][m])
		





	return 


	
def build_CFG():

    main_addr = p.project.loader.main_object.get_symbol('main').rebased_addr
    #p.cfg = p.project.analyses.CFGEmulated(starts=[main_addr],initial_state = p.project.factory.blank_state())
    p.cfg = p.project.analyses.CFGEmulated(starts=[main_addr],initial_state = p.project.factory.blank_state(),normalize=True,fail_fast=True,keep_state=True,context_sensitivity_level=2)
    #p.cfg = p.project.analyses.CFGFast()
    plot_cfg(p.cfg, "example_cfg_asm", asminst=True, vexinst=False, debug_info=False, remove_imports=True, remove_path_terminator=True)
    plot_cfg(p.cfg, "example_cfg_vex", asminst=False, vexinst=True, debug_info=False, remove_imports=True, remove_path_terminator=True)
    p.nodes_list = list(p.cfg.graph.nodes)
          						
			
def disassemble():
	p.binaryfile = os.path.realpath(p.args.input)

	# generate objdump file
	p.asmfile = p.binaryfile + "_asm"
	#print(info.asmfile)
	tmpfile = "/tmp/" + os.path.basename(p.asmfile)
	#print(tmpfile)
	comm = "objdump -d " + p.binaryfile + " > " + tmpfile
	os.system(comm)
	if os.path.exists(tmpfile):
		if (os.path.exists(p.asmfile) and not filecmp.cmp(tmpfile, p.asmfile)) or not os.path.exists(p.asmfile):
			comm = "objdump -d " + p.binaryfile + " > " + p.asmfile
			os.system(comm)


def parse_parameters():
	parser = argparse.ArgumentParser(description='SelectiveTaint static analysis')
	parser.add_argument("-input", help = "input enclave binary file", type=str, required=True)
	parser.add_argument("-debug", help = "to debug file", type=str, required=True)
	p.args = parser.parse_args()

def load_binary():
	file_command_return_string = subprocess.check_output(['file', p.args.input]).decode('utf-8')
	#p.debug = True
	#if info.args.input.endswith(".so"):
	if "shared object" in file_command_return_string and "dynamically linked" in file_command_return_string:
		p.picflag = 1
	else:
		p.picflag = 0

	try:
		p.project = angr.Project(p.args.input,load_options={'auto_load_libs': False})
	except:
		p.picflag = 0
		p.project = angr.Project(p.args.input, 
			main_opts = {'backend': 'blob'},
			load_options={'auto_load_libs': False})
    

parse_parameters()
load_binary()
disassemble()
build_CFG()
Topo(p.nodes_list)



# print(type(p.nodes_list[0]))
# for n in p.nodes_list:
# 	print(hex(n.addr), n.syscall_name)