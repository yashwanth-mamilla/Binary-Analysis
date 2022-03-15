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
        
        self.regs = dict()
        self.mem = dict()
        self.storeIns = set()
        self.func = None
		
        self.esp = 24
        self.ebp = 28
        self.debug = False
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
		
def parse_data(expr, nodeAddr, tempVar_map):

	flag = False
	val = None
	
	#print(expr.tag,expr)
	if expr.tag == "Iex_Const" :
		flag=True
		
		val = (expr.con.value)
			
	if expr.tag == 'Iex_RdTmp' :
		if expr.tmp in tempVar_map :
			flag=True
			val = tempVar_map[expr.tmp]	
	if expr.tag == 'Iex_Get' :
		if expr.offset in p.bb_info[nodeAddr]['regs'] :
			flag = True 
			val = p.bb_info[nodeAddr]['regs'][expr.offset]
			#p.regs[expr.offset] 
		else :
			print("loading from uninitialized register")	
	if expr.tag == 'Iex_Load' :
		flag1,addr = parse_data(expr.addr, nodeAddr, tempVar_map)	
		if flag1 :
			flag = True
			val = 0
			# print("\nIN LOAD :")
			# print(p.storeInsns_map[nodeAddr])
			# print(str(hex(addr)))

			if str(hex(addr)) not in p.storeInsns_map[nodeAddr] :
				#print("Loading addr : " + str(hex(addr)))
				print("at " + hex(p.curr_asm_ins))
				if(int(addr)==0):
					return (flag1,val)
				else :
					loading_offset_addr = 0x100000000-int(addr)
				print("ebp = esp "+str(p.bb_info[nodeAddr]['regs'][28]))
				print("Use of Uninitialized Mem loc at esp - " + str(hex(loading_offset_addr)))
						
		
	if expr.tag == 'Iex_Binop' :
		flag1,data1 = parse_data(expr.args[0], nodeAddr, tempVar_map)
		flag2,data2 = parse_data(expr.args[1], nodeAddr, tempVar_map)
		op = expr.op
		#print(op)
		if(op == 'Iop_Add32' and check(flag1,flag2) ):
			flag = True
			val = data1+data2
		if(op == 'Iop_Sub32' and check(flag1,flag2)) :
			flag = True
			val = data1-data2
		if(op =='Iop_And32' and check(flag1,flag2)) :
			flag=True
			val = data1 & data2
		if(op =='Iop_CmpEQ32' and check(flag1,flag2)) :
			flag=True
			val = data1 == data2
		if(op =='Iop_CmpNE32' and check(flag1,flag2)) :
			flag=True
			val = data1 != data2
		if(op =='Iop_CmpLE32S' and check(flag1,flag2)) :
			
			flag=True
			val = data1 <= data2
		if(op =='Iop_CmpLE32U' and check(flag1,flag2)) :
			
			flag=True
			val = data1 <= data2
		if(op =='Iop_CmpLT32S' and check(flag1,flag2)) :
			
			flag=True
			val = data1 < data2
		if(op =='Iop_CmpLT32U' and check(flag1,flag2)) :
			flag=True
			val = data1 < data2
		#print(op)
	if expr.tag == 'Iex_Unop' :
		flag1,data1 = parse_data(expr.args[0], nodeAddr, tempVar_map)
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
	
def parse_stmts(stmt, nodeAddr, tempVar_map):

	if(p.debug):
		print(stmt.tag,stmt)
	storeIns = set()        
	if stmt.tag == 'Ist_IMark' :
		p.curr_asm_ins = stmt.addr        
	if stmt.tag == 'Ist_Put' :
		flag,data = parse_data(stmt.data, nodeAddr, tempVar_map)
		#print(flag,data)
		if flag and data != None :
			p.bb_info[nodeAddr]['regs'][stmt.offset]=data
			#p.regs[stmt.offset] = data
		# if stmt.offset == 28 :
		# 	p.regs[28] = 0
		# else :
		# 	p.regs[stmt.offset] = data
	if stmt.tag == 'Ist_WrTmp':
		flag,data = parse_data(stmt.data, nodeAddr, tempVar_map)
		#print(flag,data)
		if flag and data != None :
			tempVar_map[stmt.tmp] = data
	if stmt.tag == 'Ist_Store' :
		flag,addr = parse_data(stmt.addr, nodeAddr, tempVar_map)
		flag1,data = parse_data(stmt.data, nodeAddr, tempVar_map)
		if flag :
			#print(str(hex(p.curr_asm_ins))+" storing addr : " + str(hex(addr)))
			storeIns.add(hex(addr))
	if(p.debug) : 	
		print(tempVar_map)
		print(p.bb_info[nodeAddr]['regs'])
		print(storeIns)
		print('\n\n') 
	return storeIns   	


def BFS(nodes_list):
	
	queue = []
	queue.append(nodes_list[0])
	
	while len(queue) :
		sz = len(queue)
		print(sz, "...........")
		storeInsns = set()
		while sz:
			node = queue.pop(0)
			for s in node.successors:
				queue.append(s)

			try:
				stmts = node.block.vex.statements
			except:
				stmts = []

			tempVar_map = dict()
			p.curr_asm_ins = None
			storeInsn = set()
			for stmt in stmts :
				l = parse_stmts(stmt,tempVar_map)
				for i in l:
					storeInsn.add(i)

			if len(storeInsns) == 0:
				for i in storeInsn:
					storeInsns.add(i)
			else:
				storeInsns = storeInsns.intersection(storeInsn)

			sz -= 1
		p.storeIns.update(storeInsns)
		#print(p.storeIns)

def Topo(nodes_list):
	

	next_nodes = [nodes_list[0]]

	in_degree = dict()
	vis_map = dict()

	for i in nodes_list : 
		vis_map[i.addr] = []
		in_degree[i.addr] = len(i.predecessors)
		p.storeInsns_map[i.addr] = set()
		p.bb_info[i.addr] = dict()
		p.bb_info[i.addr]['regs'] = dict()
		p.bb_info[i.addr]['regs'][24] = 0
		p.bb_info[i.addr]['regs'][28] = 0
		

	while next_nodes :

		node = next_nodes.pop(0)

		if len(node.predecessors) > 0 : 
			p.storeInsns_map[node.addr] = p.storeInsns_map[node.predecessors[0].addr].copy()

			p.bb_info[node.addr]['regs'] = p.bb_info[node.predecessors[0].addr]['regs'].copy()
			for pre in node.predecessors:
			
				p.storeInsns_map[node.addr] = p.storeInsns_map[node.addr].intersection(p.storeInsns_map[pre.addr])	
				
		try:
			stmts = node.block.vex.statements
		except:
			stmts = []

		tempVar_map = dict()
		for stmt in stmts :
			l = parse_stmts(stmt, node.addr, tempVar_map)

			for i in l :
				p.storeInsns_map[node.addr].add(i)

		for suc in node.successors : 
			in_degree[suc.addr] -= 1
			if in_degree[suc.addr] == 0:
				next_nodes.append(suc)
	return


	
def build_CFG():

    main_addr = p.project.loader.main_object.get_symbol('main').rebased_addr
    p.cfg = p.project.analyses.CFGEmulated(starts=[main_addr],initial_state = p.project.factory.blank_state())
    
    plot_cfg(p.cfg, "example_cfg_asm", asminst=True, vexinst=False, debug_info=False, remove_imports=True, remove_path_terminator=True)
    plot_cfg(p.cfg, "example_cfg_vex", asminst=False, vexinst=True, debug_info=False, remove_imports=True, remove_path_terminator=True)
    nodes = p.cfg.graph.nodes
    # p.regs[p.esp]=0
    # p.regs[p.ebp]=0

    #p.regs[p.ebp]=0
    p.nodes_list = list(nodes)



    
    # for i in range(len(nodes)) :
    #     node = nodes_list[i]
    #     #print(hex(node.addr))
    #     try:
    #         stmts = node.block.vex.statements
    #     except:
    #         stmts = []
        
    #     tempVar_map = dict()
        
    #     p.curr_asm_ins = None
    #     #continue
    #     for stmt in stmts :
    #     	parse_stmts(stmt,tempVar_map)
          						
			
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