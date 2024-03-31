#include <bits/stdc++.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>
#include <regex>

#include <isl/arg.h>
#include <isl/ctx.h>
#include <isl/options.h>
#include <isl/union_set.h>
#include <isl/schedule_node.h>

#include "ppcg/pet/options.h"
#include "ppcg/pet/scop.h"
#include "ppcg/pet/scop_yaml.h"

// Define a macro for error handling
#define CHECK_NULL(pointer, message) \
    if ((pointer) == NULL) { \
        fprintf(stderr, "Error: %s\n", message); \
        return -1; \
    }
#define BUFFER_SIZE 1024 // Increased buffer size

#define IDT(n) for (int i = 0; i < n; i++) printf(" ");

char *sim_prog_path;  // argv[1]
char *exe_prog_path;  // argv[2]
char *pet_prog_args;  // argv[3]
std::vector<std::pair<const char *, int>> var_n_val;

typedef std::uint64_t hash_t;
constexpr hash_t prime = 0x100000001B3ull;  
constexpr hash_t basis = 0xCBF29CE484222325ull;  
  
hash_t hash_( char const * str)   
{  
    hash_t ret{basis};  
   
    while (*str){  
        ret ^= *str;  
        ret *= prime;  
        str++;  
    }  
   
    return  ret;  
}

constexpr hash_t hash_compile_time( char const * str, hash_t last_value = basis)   
{  
    return  *str ? hash_compile_time(str+1, (*str ^ last_value) * prime) : last_value;  
}  

enum accessType{
    WRITE,
    READ,
    CONSTANT
};

typedef enum isl_schedule_node_type isl_schedule_node_type;

typedef struct{
  /* Name of the array 
   * A little bit useless but we still preserver it 
   * Since debug print it could provide infos
   */
  char *name;
  /* 
   * Different with var_n_val<const char *, int> 
   * This element describe the whole size of array
   * Not limited to the iteration space 
   * It is not like the iteration space
   * An array always have its start address from 0
   */
  std::set<std::pair<const char *, int> *> *var_n_val;
  /* The start of array, for calculation, known till addr gen */
  unsigned long long int start_addr;
  /* Use the array size to calculate the offset from start */
  long long int offset;
  /* When will this array reference first occur? Compute by band and num of accesses */
  long long int first_occur;
  /* What is the item of the first occurrence? */
  isl_union_map *first_access;
} ArrayRef;

/* Struct for memory access                       */
/* Small item per access serves for accessPerStmt */
typedef struct{
    int indent;
    int lineno;
    accessType type;
    std::string arrarName;
    isl_union_map *access;
} MemoryAccess;

typedef std::vector<std::pair<int, std::vector<MemoryAccess *> *> *> accessPerStmt;

typedef struct {
  /* name of the loop index from S[ x, x, x ... ] */
  char *index;
  /* May be less than or equal less than. */
  int is_lt;
  /* May be greater than or equal greater than. */
  int is_gt;
  char *ub;
  char *lb;
  long int ub_val;
  long int lb_val;
} indexBound;

typedef struct  {
  /* Which statement? */
  int stmt_no;
  /* the {Sn[x, x, x, ...] : constraints ; ... }, the x part, vars for inequality */
  char **names;
  /* Number of indexBound, also the number of constraints (in dom) */
  int ib_num;
  /* the constraint part, the constraint for each stmt */
  indexBound** ib;
  /* For finding the lexmin, the union set */
  isl_union_set *iter_space;
} stmtSpace;

typedef struct {
  /* The number of the statement */
  int stmt_num;
  /* Number of undetermined vars */
  int var_num;
  /* number of array structure this program */
  int array_num;
  /* The address of the statement */
  stmtSpace **stmt;
  /* the [x, x, x, ...] -> { ... }, the x part, vars for inequality */
  char **variables;
  /* For tree construction, take on the accessPerStmt 
   * Data is from pet tree, stores all stmt_no pair and accesses (list) for each stmt, 
   * a list of pair of (int and) list
   */
  accessPerStmt *mem_access;
  /* All array structure member of the whole program */
  // ArrayRef **array_refs;
  std::unordered_map<std::string, ArrayRef *> *array_refs;
} domainSpace;

typedef struct {
  /* The domain of the tree */
  domainSpace *dom;
  /* Which access is it now? */
  std::stack<int> *curr_access;
} dom_and_count;

typedef struct extTree extTree;
struct extTree {
  isl_schedule_node_type type;
  /* All data to construct the Tree */
  domainSpace *dom;
  /* The ancestor fo the tree node */
  extTree *parent;
  /* The children of the tree node. 
   * Or for leaf node, this is the  access relations
   */
  union {
    MemoryAccess **access_relations;
    extTree **children;
  };
  /* The number of children */
  int child_num;
  /* Current at which children */
  int curr_stmt;
  /* For sim information, the index bound this band */
  indexBound *ib;
  /* For sim phase, should recalc everytime the execution time */
  int execution_time;
  /* For sim phase, which time already executed? */
  int curr_exec_time;
} ;

/* The initializer starts */
indexBound *init_indexBound() {
  indexBound *bound = (indexBound *)(malloc(sizeof(indexBound)));
  bound->index = NULL;
  bound->is_lt = 0;
  bound->is_gt = 0;
  bound->ub = NULL;
  bound->lb = NULL;
  bound->ub_val = -1;
  bound->lb_val = -1;
  return bound;
}

stmtSpace *init_stmtSpace(int stmt_no, int ib_num) {
  stmtSpace *stmt = (stmtSpace *)(malloc(sizeof(stmtSpace)));
  stmt->stmt_no = stmt_no;
  stmt->ib_num = ib_num;
  stmt->names = (char **)(malloc(10 * sizeof(char *)));
  stmt->ib = (indexBound **)(malloc(10 * sizeof(indexBound *)));
  return stmt;
}

domainSpace *init_domainSpace() {
  domainSpace *dom = (domainSpace *)(malloc(sizeof(domainSpace)));
  accessPerStmt *mem_access = NULL;
  dom->stmt_num = 0;
  dom->var_num = 0;
  dom->array_num = 0;
  dom->stmt = (stmtSpace **)(malloc(10 * sizeof(stmtSpace *)));
  dom->variables = (char **)(malloc(10 * sizeof(char *)));
  dom->array_refs = new std::unordered_map<std::string, ArrayRef *>();
  return dom;
}

extTree *init_extTree(domainSpace *dom, extTree *parent) {
  extTree *tree = (extTree *)(malloc(sizeof(extTree)));
  tree->type = isl_schedule_node_error;
  tree->dom = dom;
  tree->parent = parent;
  tree->children = (extTree **)(malloc(10 * sizeof(extTree *)));
  tree->child_num = 0;
  if (parent != NULL)
    tree->curr_stmt = parent->curr_stmt;
  else
    tree->curr_stmt = 0;
  return tree;
}

ArrayRef *init_ArrayRef(std::string name) {
  ArrayRef *array = (ArrayRef *)(malloc(sizeof(ArrayRef)));
  array->name = (char *)(malloc(name.length() + 1));
  strcpy(array->name, name.c_str());
  array->var_n_val = new std::set<std::pair<const char *, int> *>();
  array->start_addr = 0;
  array->first_occur = 0;
  array->first_access = NULL;
  return array;
}

dom_and_count *init_dom_and_count(domainSpace *dom) {
  dom_and_count *dc = (dom_and_count *)(malloc(sizeof(dom_and_count)));
  dc->dom = dom;
  dc->curr_access = new std::stack<int>();
  return dc;
}

/*
 * Parse the DWARF information from the binary
 * @param out char **unit: the array of compiled source path
 * @return int: number of compilation unit
 */
int parse_dwarf(char **unit, FILE *fp) {

  int compilation_unit = 0;
  char path[1035];
  char prev_line[1035] = "";
  
  //init the array, assume there's only 10 compilation unit
  for (int i = 0; i < 10; i++) {
    unit[i] = NULL;
  }

  // Read the output line by line and process it
  while (fgets(path, sizeof(path), fp) != NULL) {
      // Check if the current line contains DW_AT_name
      // printf("%s\n\n", path);
      // Check if the previous line contains DW_AT_comp_dir
      if (strstr(prev_line, "DW_AT_name") != NULL) {
          // Print DW_AT_name and DW_AT_comp_dir
      }
      if (strstr(path, "DW_AT_comp_dir") != NULL) {
        // printf("touched\n");
        // printf("%s", prev_line);
        // printf("%s", path);
        char *colon_pos_name = strchr(prev_line, ':');
        for (int i = 0; i < 2 && colon_pos_name != NULL; i++) {
            colon_pos_name = strchr(colon_pos_name + 1, ':');
        }
        colon_pos_name += 2;
        colon_pos_name[strcspn(colon_pos_name, "\n")] = '\0';
        if (colon_pos_name != NULL) {
            // is a inclue path
            if (compilation_unit) {
                unit[compilation_unit] = (char *)(malloc(strlen(colon_pos_name) + 1));
                // copy content and discard contents after 
                char *last_slash = strrchr(colon_pos_name, '/');
                if (last_slash != NULL) {
                    //remove last_slash in colon_pos_name
                    *last_slash = '\0';
                } 
                strcpy(unit[compilation_unit], colon_pos_name);
            // Where tha main at
            } else {
                unit[compilation_unit] = (char *)(malloc(strlen(colon_pos_name) + 1));
                strcpy(unit[compilation_unit], colon_pos_name);
            }
            compilation_unit++;
        }
      }
      // Save the current line to prev_line
      strcpy(prev_line, path);
  }

  // Close the pipe
  pclose(fp);
  return compilation_unit;
}

void replaceString(char *str, const char *oldSubstr, const char *newSubstr) {
    char *pos = strstr(str, oldSubstr);
    if (pos != NULL) {
        int oldSubstrLen = strlen(oldSubstr);
        int newSubstrLen = strlen(newSubstr);
        memmove(pos + newSubstrLen, pos + oldSubstrLen, strlen(pos + oldSubstrLen) + 1);
        memcpy(pos, newSubstr, newSubstrLen);
    }
}

/*
 * Instead of calculating the schedule from the pet_scop, we can use ppcg to do that
 * @param out char *arg_list: the list of argument to pass to ppcg
 * @param int compilation_unit: the number of compilation unit
 * @return int arg_count: the number of arguments for ppcg
 */
int get_computed_sched_from_ppcg(char **unit, char *ret, int compilation_unit) {
  int arg_count = 0;
  const char *incl = "-I";

  char ppcg_args[BUFFER_SIZE/2] = {0};
  char ppcg_call[BUFFER_SIZE] = {0};

  // Concatenate all args to make a ppcg call
  for (int i = 0; i < compilation_unit; i++) {
    if (i)
      strcat(ppcg_args, incl);
    strcat(ppcg_args, unit[i]);
    strcat(ppcg_args, " ");
    arg_count++;
  }

  char sched[BUFFER_SIZE/4];
  strcpy(sched, sim_prog_path);
  char newSubstr[] = "/schedule/";
  char addition[] = ".sched";
  
  // Step 1: Replace "/obj/" with "/schedule/"
  replaceString(sched, "/obj/", newSubstr);

  // Step 2: Append "sched" at the end
  strcat(sched, addition);
  // strcat(ppcg_call, "--save-schedule=/home/dreyex/use_this/schedule/jacobi-2d.sched");
  
  // A "--no-reschedule" flag is added to prevent ppcg from rescheduling the program
  snprintf(ppcg_call, BUFFER_SIZE-1, "%s/ppcg %s --no-reschedule --save-schedule=%s", exe_prog_path, ppcg_args, sched);
  #ifdef DEBUG
  printf("ppcg call: %s\n", ppcg_call);
  #endif
  FILE *fp;
  fp = popen(ppcg_call, "r");
  if (fp == NULL) {
      printf("Failed to run command\n");
      ret = NULL;
  } else {
    strcpy(ret, sched);
  }
  pclose(fp);

  return arg_count;
}

std::list<std::string> split(const std::string &s, const char delimiter, 
                             const std::string start, const std::string end) {
  size_t start_pos = 0;
  size_t end_pos = 0;
  std::list<std::string> tokens;
  std::string token;
  std::string *parse_arget = new std::string(s);
  start_pos = parse_arget->find(start);
  end_pos = parse_arget->find(end);
  token = parse_arget->substr(start_pos + 1, end_pos - start_pos - 1);
  std::istringstream tokenStream(token);
  // while (std::getline(tokenStream, token, delimiter)) {
  for (std::string token; std::getline(tokenStream, token, delimiter);){
    // if token starts or ends with space, remove it
    if (token[0] == ' ') {
      token.erase(0, 1);
    }
    if (token[token.length() - 1] == ' ') {
      token.erase(token.length() - 1, 1);
    }
    tokens.push_back(token);
  }
  return tokens;
}

std::list<std::string> split_by_str(const std::string &s, const std::string delimiter, 
                                    const std::string start, const std::string end) {
  size_t start_pos = 0;
  size_t end_pos = 0;
  std::list<std::string> tokens;
  std::string token;
  std::string *parse_arget = new std::string(s);
  start_pos = parse_arget->find(start);
  end_pos = parse_arget->find(end);
  token = parse_arget->substr(start_pos + 1, end_pos - start_pos - 1);
  while (token.find(delimiter) != std::string::npos) {
    size_t pos = token.find(delimiter);
    tokens.push_back(token.substr(0, pos));
    token.erase(0, pos + delimiter.length());
  }
  tokens.push_back(token);
  return tokens;
}

inline void parse_inequality(const std::string &s, stmtSpace *stmt){
  // std::cout << "S" << stmt->stmt_no << " parsing: " << s  << "(whole token)" << std::endl; 
  std::string tok = "<";
  int occurrences = 0;
  size_t pos = 0;
  size_t temp = 0;
  size_t index_pos = std::string::npos;
  int index_var = -1;
  // Find which index this inequality is for
  /* Some Rules I've figured out later: 
   * The index var comes first than the bound var in the inequality
   * But constant bound is not limited to this rule
   * So we need to find the index var that have the smaller index_pos
   * Rather than the first one we've found
   */
  for (int i = 0; i < stmt->ib_num; i++) {
    temp = s.find(stmt->names[i]);
    if (temp < index_pos) {
      // This is the index
      index_pos = temp;
      index_var = i;
    }
  }
  if (index_var == -1) {
    std::cout << "Error: index_var not found" << std::endl;
    return;
  }
  // std::cout << "handle: " << stmt->names[index_var] << std::endl;

  // Find which inequality it is (2 or 3 elements?)
  while ((pos = s.find(tok, pos )) != std::string::npos) {
          ++ occurrences;
          pos += tok.length();
  }
  // std::cout << "occurrences: " << occurrences << std::endl;

  if (occurrences == 2) {
    // Find contents from initial to the first "<"
    size_t pos = s.find("<");
    // Start from 1, bypass the space
    std::string elem = s.substr(1, pos-1);
    stmt->ib[index_var]->lb = (char *)(malloc(elem.length() + 1));
    strcpy(stmt->ib[index_var]->lb, elem.c_str());
    // If the next char is "=", then it's less than or equal
    if (s[pos + 1] == '=') 
      stmt->ib[index_var]->is_lt = 0;
    else
      stmt->ib[index_var]->is_lt = 1;
    // Find contents from the second "<" to the end 
    pos = s.find("<", pos + 1);
    if (s[pos + 1] == '=') {
      stmt->ib[index_var]->is_gt = 0;
      // Bypass the "="
      pos++;
    }
    else
      stmt->ib[index_var]->is_gt = 1;
    // Bypass the " "
    pos++;
    elem = s.substr(pos + 1, s.length() - pos - 1);
    stmt->ib[index_var]->ub = (char *)(malloc(elem.length() + 1));
    strcpy(stmt->ib[index_var]->ub, elem.c_str());
    // If the next char is "=", then it's less than or equal
  } 
  else {
    // Occurrence == 1 or 0, since "<" not exists in ">" case
    size_t pos = s.find("=");
    int big = -1;
    // The founded one is smaller
    s.find(">") > s.find("<") ? big = 0 : big = 1;
    // std::cout << "big: " << big << std::endl;
    if (pos == std::string::npos) // Very sure is gt or lt
      big ? stmt->ib[index_var]->is_lt = 1 : stmt->ib[index_var]->is_gt = 1;
    else
      big ? stmt->ib[index_var]->is_lt = 0 : stmt->ib[index_var]->is_gt = 0;
    // std::cout << "is_lt: " << stmt->ib[index_var]->is_lt << std::endl;
    // std::cout << "is_gt: " << stmt->ib[index_var]->is_gt << std::endl;
    big ? pos = s.find(">") : pos = s.find("<");
    // std::cout << "pos: " << pos << std::endl;
    // get over the sign, take the val
    std::string elem = s.substr(pos+2, s.size());
    // std::cout << "elem: " << elem << std::endl;
    big ? stmt->ib[index_var]->lb = (char *)(malloc(elem.length() + 1)) : 
          stmt->ib[index_var]->ub = (char *)(malloc(elem.length() + 1));
    big ? strcpy(stmt->ib[index_var]->lb, elem.c_str()) :
          strcpy(stmt->ib[index_var]->ub, elem.c_str());
  }
}

inline void compensate(stmtSpace *stmt, int index, int is_ub){
  if (is_ub) {
    // Upper bound is null? Might be someone's lower bound
    for (int i = 0; i < stmt->ib_num; i++) {
      if (stmt->ib[i]->lb != NULL && !strcmp(stmt->ib[i]->lb, stmt->ib[index]->index)) {
        stmt->ib[index]->ub = (char *)(malloc(strlen(stmt->ib[i]->ub) + 1));
        strncpy(stmt->ib[index]->ub, stmt->ib[i]->ub, strlen(stmt->ib[i]->ub));
      }
    }
  } else {
    // Lower bound is null
    for (int i = 0; i < stmt->ib_num; i++) {
      if (stmt->ib[i]->ub != NULL && !strcmp(stmt->ib[i]->ub, stmt->ib[index]->index)) {
        stmt->ib[index]->lb = (char *)(malloc(strlen(stmt->ib[i]->lb) + 1));
        strncpy(stmt->ib[index]->lb, stmt->ib[i]->lb, strlen(stmt->ib[i]->lb));
      }
    }
  }
}

/*
 * Extract the domain each statement from the schedule
 * @param in FILE *file: the file to extract the domain from
 * @param out stmtSpace *dom: the domain of each statement
 */
int extract_dom_from_sched(FILE *file, domainSpace *dom) {
  char line[BUFFER_SIZE];
  int var_num = 0;
  int status = 0;
  // We only get the first line of the file and parse it
  fgets(line, sizeof(line), file);
  // Starts to parse the domain
  // Some input like this: 
  // domain: "[tsteps, n] -> { S1[t, i, j] : 0 <= t < tsteps and 0 < i <= -2 + n and 0 < j <= -2 + n; S2[t, i, j] : 0 <= t < tsteps and 0 < i <= -2 + n and 0 < j <= -2 + n }"
  // First parse the variable part: [tsteps, n]
  std::cout << "start parsing line: " << line << std::endl;
  std::list<std::string> tokens = split(line, ',', "[", "]");
  for (std::list<std::string>::iterator it = tokens.begin(); it != tokens.end(); it++) {
    // copy to dom variable
    dom->variables[var_num] = (char *)(malloc(it->length() + 1));
    strcpy(dom->variables[var_num], it->c_str());
    var_num++;
  }
  dom->var_num = var_num;
  // Then parse the domain part
  tokens = split(line, ';', "{", "}");
  int curr_stmt = 0;

  // For each stmt iterate:
  for (std::list<std::string>::iterator it = tokens.begin(); it != tokens.end(); it++) {
    int num_iter = 0;
    sscanf(it->c_str(), "S%d%*s", &curr_stmt);
    std::list<std::string> iters = split(*it, ',', "[", "]");
    std::list<std::string> constraints = split_by_str(*it, "and", ":", ";");
    stmtSpace *stmt = init_stmtSpace(curr_stmt, iters.size());
    for (auto nn : iters) {
      indexBound *bound = init_indexBound();
      bound->index = (char *)(malloc(nn.length() + 1));
      strcpy(bound->index, nn.c_str());
      stmt->ib[num_iter] = bound;
      stmt->names[num_iter] = bound->index;
      num_iter++;
    }
    stmt->ib_num = num_iter;

    // Parse the inequality (constraint part)
    for (auto c : constraints) {
      parse_inequality(c, stmt);
    }
    // Compensation for unfound upper/lower bound:
    for (int i = 0; i < stmt->ib_num; i++) {
      if (stmt->ib[i]->ub == NULL)  compensate(stmt, i, 1);
      else if (stmt->ib[i]->lb == NULL) compensate(stmt, i, 0);
    }
    dom->stmt[dom->stmt_num] = stmt;
    dom->stmt_num++;
  }
  status = 1;
  // Could iterate through the list till the end
  dom->stmt[dom->stmt_num + 1] = NULL;
  return status;
}

int parse_dwarf_calc_bound(FILE *fp, domainSpace *dom) {
  int status = 0;
  int skip = 1;
  int found = 0;
  char buffer[BUFFER_SIZE];
  char target[32];
  char *to_write;
  const char *long_mode = "    <%*x>   DW_AT_name        : (indirect string, offset: 0x%*x): %s";  
  const char *short_mode = "    <%*x>   DW_AT_name        : %s";
  // The rule of dwarf:
  // One element starts with line which the buf[1] is "<"
  // Then the following line is the attribute, which DW_AT_name is the first attribute of the elem
  // If the DW_AT_name matches the variable name, we want to find the DW_AT_const_value 5 lines after
  while (fgets(buffer, sizeof(buffer), fp) != NULL){
    if (buffer[1] == '<') {
      // New element, can do more detail check
      if (strstr(buffer, "DW_TAG_variable") == NULL){
        skip = 1;
        continue;
      }
      skip = 0;
      continue;
    }
    if (skip) continue;
    // Check if the current line contains DW_AT_name
    if (strstr(buffer, "DW_AT_name") == NULL){
      skip = 1;
      continue;
    } else {
      // Check if the DW_AT_name matches the variable name
      if (strlen(buffer) > 50){
        // use long parse string mode
        sscanf(buffer, long_mode, target);
      } else {
        // use short parse string mode
        sscanf(buffer, short_mode, target);
      }
      // Check if the DW_AT_name matches any variable name
      for (int i = 0; i < dom->var_num; i++){
        if (!strcmp(dom->variables[i], target)){
          found = 1;
          to_write = (char *)(malloc(strlen(target) + 1));
          strcpy(to_write, target);
          for (int j = 0; j < 5; j++){
            fgets(buffer, sizeof(buffer), fp);
          }
          if (strstr(buffer, "DW_AT_const_value") != NULL){
            int val;
            sscanf(buffer, "    <%*x>   DW_AT_const_value : %d", &val);
            var_n_val.push_back(std::make_pair(to_write, val));
            break;
          }
          break;
        }
      }if (!found){
        skip = 1;
        continue;
      }
      // Else, a matched on is found, create an table elem to subsitute content
    }
  }
  status = 1;
  return status;
}

/*
 * Calculate the value of the variable
 * @param in const char *var: the variable name
 * @return int: the "actual calculated" value of the variable
 */
int calc_eq(const char *var) {
  // tokenize the var, make all elem to list, sepqrate by " "
  long int temp_val = 0;
  long int val = 0;
  char *endptr;
  std::list<std::string> tokens;
  std::string token;
  // WIP: This Line Is Not Safe!!!
  if (var == NULL) {
    std::cout << "Error: var is NULL" << std::endl;
    return -1;
  }
  std::string *parse_arget = new std::string(var);
  size_t pos = 0;
  while ((pos = parse_arget->find(" ")) != std::string::npos) {
    token = parse_arget->substr(0, pos);
    tokens.push_back(token);
    parse_arget->erase(0, pos + 1);
  }
  tokens.push_back(*parse_arget);
  //Dump the list
  for (std::list<std::string>::iterator it = tokens.begin(); it != tokens.end(); it++) {
    // temp_val = atoi(it->c_str());
    temp_val = strtol ( it->c_str() , &endptr , 10 ) ;
    if (*endptr != '\0') {
      // Two cases: operator or number
      // Operator
      if (!strcmp(it->c_str(), "+") || !strcmp(it->c_str(), "-")
          || !strcmp(it->c_str(), "*") || !strcmp(it->c_str(), "/")) {
        continue;
      } else {
        // Might have subsitution
        for (auto p : var_n_val) {
          if (!strcmp(p.first, it->c_str())) {
            // std::cout << "substituting: " << it->c_str() << " to " << p.second << std::endl;
            temp_val = p.second;
            val += temp_val;
            break;
          }
        }
      }
    } else {
      val += temp_val;
    }
    temp_val = 0;
  }
  // std::cout << "val: " << val << std::endl;
  return val;

}

int calc_dom_bound(domainSpace *dom) {
  // First dump all ib in dom
  #ifdef DEBUG
  for (int i = 0; i < dom->stmt_num; i++) {
    stmtSpace *stmt = dom->stmt[i];
    std::cout << "S" << stmt->stmt_no << std::endl;
    for (int j = 0; j < stmt->ib_num; j++) {
      indexBound *ib = stmt->ib[j];
      if (ib->lb != NULL)
      {std::cout << ib->lb ;
      //std::cout << "is_lt: " << dom->ib[i]->is_lt << std::endl;
      if (ib->is_lt) std::cout << " < ";
      else std::cout << " <= " ;}
      std::cout << ib->index ;
      // std::cout << "is_gt: " << dom->ib[i]->is_gt << std::endl;
      if (ib->ub != NULL)
      {if (ib->is_gt) std::cout << " < ";
      else std::cout << " <= " ;
      std::cout << ib->ub << std::endl;}
    }
  }
  #endif

  for (int i = 0; i < dom->stmt_num; i++) {
    stmtSpace *stmt = dom->stmt[i];
    for (int j = 0; j < stmt->ib_num; j++) {
      indexBound *ib = stmt->ib[j];
      ib->ub_val = calc_eq(ib->ub);
      if (ib->is_gt) ib->ub_val--;
      ib->lb_val = calc_eq(ib->lb);
      if (ib->is_lt) ib->lb_val++;
    }
  }

  return 1;
}

indexBound *find_index_bound_from_stmt(domainSpace *dom, int stmt_no, std::string index) {
  for (int i = 0; i < dom->stmt_num; i++) {
    if (dom->stmt[i]->stmt_no == stmt_no) {
      for (int j = 0; j < dom->stmt[i]->ib_num; j++) {
        if (!strcmp(dom->stmt[i]->ib[j]->index, index.c_str())) {
          return dom->stmt[i]->ib[j];
        }
      }
    }
  }
  return NULL;
}

stmtSpace *find_stmt_from_domain(domainSpace *dom, int stmt_no) {
  for (int i = 0; i < dom->stmt_num; i++) {
    if (dom->stmt[i]->stmt_no == stmt_no) {
      return dom->stmt[i];
    }
  }
  return NULL;
}

int extract_stmt_no_regex(std::string str) {
  std::regex pattern("S(\\d+)");
  std::smatch match;
  if (std::regex_search(str, match, pattern)) {
    // Extract the number after "S"
    std::string number_str = match[1];
    return std::stoi(number_str);
  }
  return -1;
}

/* ExtTree Construction callback function */
isl_bool construction(__isl_keep isl_schedule_node *node, void *upper){
  /* Construction Phase of extTree */
  extTree **upper_ptr = (extTree **)upper;
  extTree *parent = *upper_ptr;
  // Rewrite the ptr to the current node
  extTree *current = init_extTree(parent->dom, *upper_ptr);

  enum isl_schedule_node_type type;
  type = isl_schedule_node_get_type(node);
  isl_union_set *filter_temp;
  isl_union_map *band_temp;
  stmtSpace *stmt;
  std::vector<MemoryAccess *> *cur_mem_access;
  std::string isl_obj_str;
  std::regex pattern("S(\\d+)");
  std::smatch match;
  std::string index;
  int curr_stmt = 0;
  switch (type) {
    case isl_schedule_node_error:
    /* Error, terminated. */
      return isl_bool_false;
      break;
    
    /* 
      * A band node is between filter node (upper) and leaf node
      * The bound can describe how many time the leaf should execute
      * Numbers of execution preferred stored in equations, since
      * not every case the bound is represented by the "N", we shall
      * recalculate the next level of execution everytime a node has
      * done all of its execution.
      */
    case isl_schedule_node_band:
      parent->children[parent->child_num] = current;
      parent->child_num++;
      current->type = isl_schedule_node_band;
      band_temp = isl_schedule_node_get_subtree_schedule_union_map(node);
      isl_obj_str = isl_union_map_to_str(band_temp);
      // Something like band: [tsteps, n] -> { S1[t, i, j] -> [i, j] }
      if (std::regex_search(isl_obj_str, match, pattern)) {
      // Extract the number after "S"
        std::string number_str = match[1];
        curr_stmt = std::stoi(number_str);
      }
      if (curr_stmt){
        // Find from isl_obj_str, the last pair of [ and , the content between it, is the index
        size_t start_pos = isl_obj_str.find_last_of("[");
        // From this pos find the next ","
        size_t end_pos = isl_obj_str.find(",", start_pos);
        if (end_pos == std::string::npos) {
          // If not found, find the next "]"
          end_pos = isl_obj_str.find("]", start_pos);
        }
        // fetch the content between the two pos
        index = isl_obj_str.substr(start_pos + 1, end_pos - start_pos - 1);
        #ifdef DEBUG
        // std::cout << "index: " << index << " of S" << curr_stmt << std::endl;
        #endif

      }
      current->ib = find_index_bound_from_stmt(current->dom, curr_stmt, index);
      break;
    
    case isl_schedule_node_context:
      parent->children[parent->child_num] = current;
      parent->child_num++;
      current->type = isl_schedule_node_context;
      break;
    
    case isl_schedule_node_domain:
      parent->children[parent->child_num] = current;
      parent->child_num++;
      current->type = isl_schedule_node_domain;
      break;
    
    case isl_schedule_node_expansion:
      parent->children[parent->child_num] = current;
      parent->child_num++;
      current->type = isl_schedule_node_expansion;
      break;
    
    case isl_schedule_node_extension:
      parent->children[parent->child_num] = current;
      parent->child_num++;
      current->type = isl_schedule_node_extension;
      break;
    
    /*
     * Filter node points out the statements its child belongs
     * (Maybe the domainSpace shall know which stmt we're at)
     */
    case isl_schedule_node_filter:
      parent->children[parent->child_num] = current;
      filter_temp = isl_schedule_node_filter_get_filter(node);
      isl_obj_str = isl_union_set_to_str(filter_temp);
      current->curr_stmt = extract_stmt_no_regex(isl_obj_str);
      stmt = find_stmt_from_domain(current->dom, current->curr_stmt);
      stmt->iter_space = isl_union_set_copy(filter_temp);
      // fetch stmt_no from the isl_obj_str
      // printf("stmt_no: %d\n", curr_stmt);
      isl_union_set_free(filter_temp);
      current->type = isl_schedule_node_filter;
      // Is a hint follow by the sequence node
      parent->children[parent->child_num] = current;
      parent->child_num++;
      break;

    /*
     * Leaf node is the end of the branch of schedule
     * which contains the access relations.
     * Number of times to execute is determined by the band node.
     * 
     * In phase of construct, we shall go back to the sequence 
     * where we from, since the next member of traversal is the 
     * next sequence item. However, the item has no instance yet.
     */
    case isl_schedule_node_leaf:
      parent->children[parent->child_num] = current;
      parent->child_num++;
      current->type = isl_schedule_node_leaf;
      // From accessPerStmt in domainSpace find the access of this stmt
      curr_stmt = 0;
      for (auto v : *current->dom->mem_access) {
        if (v->first == current->curr_stmt) {
          break;
        } else {
          curr_stmt++;
        }
      }
      cur_mem_access = current->dom->mem_access->at(curr_stmt)->second;
      current->access_relations = (MemoryAccess **)(malloc(cur_mem_access->size() * sizeof(MemoryAccess *)));
      for (auto v : *cur_mem_access) {
        // Do something with the access relation
        current->access_relations[current->child_num] = v;
        current->child_num++;
      }
      // Shall back to the sequence where it from
      while (parent->type != isl_schedule_node_sequence) {
        // Child Starts at 1
        parent = parent->parent;
      }
      current = parent;
      break;
    
    case isl_schedule_node_guard:
      parent->children[parent->child_num] = current;
      parent->child_num++;
      current->type = isl_schedule_node_guard;
      break;
    
    case isl_schedule_node_mark:
      parent->children[parent->child_num] = current;
      parent->child_num++;
      current->type = isl_schedule_node_mark;
      break;
    
    /*
     * Sequence node is the only node that has multiple children
     * Followed by filter node
     */
    case isl_schedule_node_sequence:
      parent->children[parent->child_num] = current;
      parent->child_num++;
      current->type = isl_schedule_node_sequence;
      current->children = (extTree **)(malloc(10 * sizeof(extTree *)));
      break;
    
    case isl_schedule_node_set:
      parent->children[parent->child_num] = current;
      parent->child_num++;
      current->type = isl_schedule_node_set;
      break;
  }
  // printf("current: %p\n", current);
  // printf("parent->child_num: %d\n", parent->child_num);
  // printf("This %d\n", current->type);
  *upper_ptr = current;

  if (isl_schedule_node_get_type(node) != isl_schedule_node_leaf)
    return isl_bool_true;

	return isl_bool_false;
}

std::string extractRefName(const std::string& str) {
  // Find positions of '->' and '['
  size_t start_pos = str.find("->");
  size_t end_pos = str.find("[", start_pos);

  // Check if both delimiters are found
  if (start_pos == std::string::npos || end_pos == std::string::npos) {
    return ""; // Return empty string if delimiters not found
  }

  // Extract substring between delimiters (exclusive)
  std::string content = str.substr(start_pos + 2, end_pos - start_pos - 2);

  // Trim leading/trailing spaces
  content.erase(std::remove_if(content.begin(), content.end(), ::isspace), content.end());

  return content;
}

int get_access_relation_from_pet(domainSpace *dom, accessPerStmt *mem_access, char **unit, int compilation_unit) {
  char arg_list[BUFFER_SIZE] = {0};
  char pet_call[BUFFER_SIZE] = {0};
  const char *incl = "-I";

  for (int i = 0; i < compilation_unit; i++) {
    if (i)
      strcat(arg_list, incl);
    strcat(arg_list, unit[i]);
    strcat(arg_list, " ");
  }

  std::cout << "arg_list: " << arg_list << std::endl;
  snprintf(pet_call, BUFFER_SIZE-1, "%s/pet %s %s", exe_prog_path, arg_list, pet_prog_args);
  char *line_ch = NULL;
  std::cout << "pet call: " << pet_call << std::endl;
  std::string line;
  std::vector<std::string> pet_tree;
  std::vector<std::string> source_code;

  /* Open the source, check the number of the Statements */
  std::ifstream source(unit[0]);
  
  FILE *pet_fp;
  pet_fp = popen(pet_call, "r");
  // push pet_fp content line by line into pet_tree
  if (pet_fp == NULL) {
    printf("Failed to run command\n");
    return 1;
  } 
  size_t line_length = 0;

  //get pet_fp line by line and save it into pet_tree
  while (getline(&line_ch, &line_length, pet_fp) != -1) {
    pet_tree.push_back(line_ch);
  }

  // push source content line by line into source_code
  if(!source.is_open()){
    printf("Failed to run command\n");
    return 1;
  }
  while(getline(source, line)){
      source_code.push_back(line);
  }

  std::vector<std::pair<int, int> *> pet_tree_tag = {};
  std::pair<int, int> *p;

  // Find the statement in the source code
  for(int i = 0; i < source_code.size(); i++){
      if(source_code[i][0] == 'S'){
          int stmt;
          std::string tag = source_code[i].substr(0, 2);
          sscanf(tag.c_str(), "S%d:", &stmt);
          // pet_tree_tag.push_back(make_pair(stmt, i+1));
          p = new std::pair<int, int>(stmt, i+1);
          pet_tree_tag.push_back(p);
      }
  }

  isl_ctx *ctx = isl_ctx_alloc();
  int cur_line = 0;
  int stmt;
  int i = 0;

  for (i; i < pet_tree.size(); i++){
      if(pet_tree[i] == "arrays:\n")
          break;
  }
  // Collect the array subscript each stmt first in case array filled out
  std::set<std::string> ind_names;
  for (int j = 0; j < dom->stmt_num; j++){
    for (int k = 0; k < dom->stmt[j]->ib_num; k++){
      if (ind_names.find(dom->stmt[j]->ib[k]->index) == ind_names.end()){
        ind_names.insert(dom->stmt[j]->ib[k]->index);
      }
    }
  }
  int arrays_start = i;
  // end of the array part is the stmt
  for (i; i < pet_tree.size(); i++){
      if(pet_tree[i] == "statements:\n")
          break;
  }
  int checkpoint = i;
  ArrayRef *array;
  auto map = dom->array_refs;
  std::unordered_map<std::string, int> established_map;
  for (int arr_i = arrays_start; arr_i < checkpoint; arr_i++){
    int pos = pet_tree[arr_i].find("extent");
    if (pos == std::string::npos) continue;
    // find string at the first "{ ", end of "[" after it
    size_t start_pos = pet_tree[arr_i].find("{");
    size_t end_pos = pet_tree[arr_i].find("[", start_pos);
    std::string array_name = pet_tree[arr_i].substr(start_pos + 2, end_pos - start_pos - 2);
    // array_name find in ind_names then continue
    if (ind_names.find(array_name) != ind_names.end()) continue;
    // std::cout << "array_name: " << array_name << std::endl; 
    array = init_ArrayRef(array_name);
    map->insert(std::pair<std::string, ArrayRef *>(array_name, array));
    established_map.insert(std::pair<std::string, int>(array_name, 0));
  }
  
  int found = 0;
  int curr_stmt = 0;
  char op[BUFFER_SIZE] = {0};
  std::cout << "i: " << i << std::endl;
  std::cout << "pet_tree.size(): " << pet_tree.size() << std::endl;
  // From now on only "- line" starts at the beginning of the line
  for(i ; i < pet_tree.size();i++){
    if(pet_tree[i][0] == '-'){
      // Dump pet_tree_tag
      // for (auto &v : pet_tree_tag){
      //     cout << v->first << " " << v->second << endl;
      // }
      sscanf(pet_tree[i].c_str(), "- line: %d", &stmt);
      // cout << "stmt: " << stmt << endl;
      for (auto &v : pet_tree_tag){
        if(v->second == stmt){
            cur_line++;
            // cout << "S" << cur_line << " " << stmt << endl;
            found = 1;
            break;
        }
      }
    }


    if(found){
      std::pair<int, std::vector<MemoryAccess *> *> *maPair = new std::pair<int, std::vector<MemoryAccess *> *>();
      std::vector<MemoryAccess *> *list = new std::vector<MemoryAccess *>();
      maPair->first = cur_line;
      maPair->second = list;
      // Start parsing the pet tree current line
      // get the line with the following format:
      // (number of blank spaces) type: (type of the statement)

      // Shall not be the next stmt catching for "type"

      i++;
      while(1){
        // Go to the line that contains "type"
        for(i; i < pet_tree.size(); i++){
            if(pet_tree[i][0] == '-')
                goto end;
            if(pet_tree[i].find("type") != std::string::npos){
                break;
            }
        }
        // Get the type of the statement
        // For example: "    type: expression" -> "expression"
        char type[20]; // Adjust size based on your needs
        char expression[100]; // Adjust size based on your needs
        char access[BUFFER_SIZE]; // Adjust size based on your needs

        // Skip leading whitespace using "%*s"
        sscanf(pet_tree[i].c_str(), "%*s%*[:]");

        // Read "type:" and the expression
        sscanf(pet_tree[i].c_str(), "%[^:]%*[: ]%s", type, expression);

        // printf("type:%s at %d\n", type, i);
        MemoryAccess *mem;
        indexBound *ib;
        isl_union_map *union_map;
        auto str = pet_tree[i];
        std::string::iterator colon_pos;
        std::string s(type);
        size_t start_pos;
        size_t end_pos;
        std::string extracted_part;
        std::list<std::string> tokens;
        mem = new MemoryAccess();
        mem->indent = s.find("- type");
        mem->lineno = i;
        char *ib_name;
        int is_write = 0;
        int has_val = 0;
        int bound_val = 0;

        switch(hash_(expression)){
          case  hash_compile_time( "access" ): 
            // cout << "Access" << endl;
            i++;
            // get the union map of access, find the first pos of ':'
            str = pet_tree[i];
            start_pos = str.find("{");
            end_pos = str.find("}");
            extracted_part = str.substr(start_pos, end_pos - start_pos+1);
            union_map = isl_union_map_read_from_str(ctx, extracted_part.c_str());
            mem->access = union_map;
            mem->arrarName = extractRefName(extracted_part);
            if (established_map.find(mem->arrarName) != established_map.end()){
              if (established_map[mem->arrarName] == 1) goto already_established;
              else established_map[mem->arrarName] = 1; // Not established before
            } 
            /* extracted part like Sn[index] -> arr[ subscript ] */
            start_pos = str.find(mem->arrarName);
            end_pos = str.find("}", start_pos);
            curr_stmt = extract_stmt_no_regex(extracted_part);
            /* [] part */
            extracted_part = str.substr(start_pos, end_pos - start_pos);
            // std::cout << "extracted_part: " << extracted_part << std::endl;
            tokens = split(extracted_part, ',', "[", "]");
            for (auto nn : tokens) {
              // remove head tail "(" and ")"
              nn.erase(0, 1);
              nn.erase(nn.size() - 1, 1);
              // std::cout << "nn: " << nn << std::endl;
              ib = find_index_bound_from_stmt(dom, curr_stmt, nn);
              if (!ib) continue;
              // find item from unordered_map and push it to the var_n_val
              for (auto p : var_n_val) {
                // if p is a substring of ib->ub, then find it
                if (ib->ub && std::string(ib->ub).find(p.first) != std::string::npos) {
                  // std::cout << "ib->ub: " << ib->ub << " p.first: " << p.first << std::endl;
                  bound_val = p.second;
                  has_val = 1;
                  break;
                }
              }
              if(has_val){
                ib_name = (char *)(malloc(nn.length() + 1));
                strcpy(ib_name, nn.c_str());
                auto pair = new std::pair<const char *, int>(ib_name, bound_val);
                if (pair) map->at(mem->arrarName)->var_n_val->insert(pair);
                // std::cout << "nn: " << nn << " bound_val: " << bound_val << " on " << mem->arrarName << std::endl;
              }
            }
            /* get the stmt no and the subscript */
already_established:
            i+=3;
            str = pet_tree[i];
            sscanf(pet_tree[i].c_str(), "%[^:]%*[: ]%d", type, &is_write);
            mem->type = is_write ? WRITE : READ;
            maPair->second->push_back(mem);
            
            break;
          case  hash_compile_time( "double" ): 
            // cout << "Double" << endl;
            mem->type = CONSTANT;
            i++;
            sscanf(pet_tree[i].c_str(), "%[^:]%*[: ]%s", type, expression);
            mem->arrarName = expression;
            // if it is a 0 then ignore
            if (!strcmp(expression, "0")) break;
            maPair->second->push_back(mem);
            // not really an array but a constant, still need the content
            array = init_ArrayRef(expression);
            map->insert(std::pair<std::string, ArrayRef *>(expression, array));
            break;
          default:
            break;
        }
        // Move to next line
        i++;
      }
end:
      found = 0;
      // reverse the vector in pair->second
      sort(maPair->second->begin(), maPair->second->end() , [](const MemoryAccess* a, const MemoryAccess* b) {
          if (a->indent != b->indent){
              return a->indent > b->indent;
          } else {
              return a->lineno > b->lineno;
          }
      });
      mem_access->push_back(maPair);
    }
  }

  pclose(pet_fp);
  return 1;
}

void dump_ib(indexBound *ib){
  std::cout << "lb: " << ib->lb << ":" << ib->lb_val 
                << " <= " << ib->index << " <="
                << " ub: " << ib->ub << ":" << ib->ub_val << std::endl;
}

void dump_node_type_str(int n){
  switch (n){
    /*-1*/case isl_schedule_node_error: std::cout << "isl_schedule_node_error" << std::endl; break;
    /* 0*/case isl_schedule_node_band: std::cout << "isl_schedule_node_band" << std::endl; break;
    /* 1*/case isl_schedule_node_context: std::cout << "isl_schedule_node_context" << std::endl; break;
    /* 2*/case isl_schedule_node_domain: std::cout << "isl_schedule_node_domain" << std::endl; break;
    /* 3*/case isl_schedule_node_expansion: std::cout << "isl_schedule_node_expansion" << std::endl; break;
    /* 4*/case isl_schedule_node_extension: std::cout << "isl_schedule_node_extension" << std::endl; break;
    /* 5*/case isl_schedule_node_filter: std::cout << "isl_schedule_node_filter" << std::endl; break;
    /* 6*/case isl_schedule_node_leaf: std::cout << "isl_schedule_node_leaf" << std::endl; break;
    /* 7*/case isl_schedule_node_guard: std::cout << "isl_schedule_node_guard" << std::endl; break;
    /* 8*/case isl_schedule_node_mark: std::cout << "isl_schedule_node_mark" << std::endl; break;
    /* 9*/case isl_schedule_node_sequence: std::cout << "isl_schedule_node_sequence" << std::endl; break;
    /*10*/case isl_schedule_node_set: std::cout << "isl_schedule_node_set" << std::endl; break;
  }
}

/*
 * Dump of the tree, also the structure to represent
 * TODO: Separate the dump and the traverse by provide print_fn to the traverse
 */
int extTree_traverse(extTree *tree, int n){
  if(tree == NULL){
    return 0;
  }
  // Main content tree node
  IDT(n) std::cout << "node type: " ;
  dump_node_type_str(tree->type);
  IDT(n) std::cout << "child_num: " << tree->child_num;
  std::cout << "/ curr_stmt: " << tree->curr_stmt << std::endl;
  if (tree->type == isl_schedule_node_band){
    IDT(n) dump_ib(tree->ib);
  }

  MemoryAccess *ar = NULL;
  for(int i = 0; i < tree->child_num; i++){
    if (tree->type != isl_schedule_node_leaf)
      extTree_traverse(tree->children[i], n+2);
    else {
      ar = tree->access_relations[i];
      // std::cout << ar->type << " " << ar->arrarName << " & ";
      if (ar->type != CONSTANT){
        char *str = isl_union_map_to_str(ar->access);
        IDT(n) std::cout << str;
        if (ar->type == READ) std::cout << " : read" << std::endl;
        else std::cout << " : write" << std::endl;
      } else {
        IDT(n) std::cout << "Constant access: " << ar->arrarName << " : read" << std::endl;
      }
    }
  }
  return 1;
}

/* Referenced from isl_schedule_foreach_schedule_node_top_down
 * Visit the root node first, then the children
 * Until there's no any children, stop
 */
int extTree_preorder_traverse(extTree *tree, int (*fn)(extTree *node, void *user, int depth), void *user, int depth){
  if(tree == NULL){
    return 0;
  }
  if (fn(tree, user, depth)){
    for(int i = 0; i < tree->child_num; i++){
      extTree_preorder_traverse(tree->children[i], fn, user, depth+1);
    }
  }
  return 1;
}

/* Referenced from isl_schedule_map_schedule_node_bottom_up, also return node ptr
 * It is the responsibility of the user to ensure that this does not
 * lead to an infinite loop.  It is safest to always return a pointer
 * to the same position (same ancestors and child positions) as the input node.
 */
extTree *extTree_postorder_traverse(extTree *tree, extTree * (*fn)(extTree *node, void *user, int depth), void *user, int depth){
  if(tree == NULL){
    return NULL;
  }
  for(int i = 0; i < tree->child_num; i++){
    if (tree->type != isl_schedule_node_leaf)
      extTree_postorder_traverse(tree->children[i], fn, user, depth+1);
  }
  if (fn(tree, user, depth)){
    return tree;
  }
  return NULL;
}

/* From original extTree_traverse, print the content of the node 
 * Callback function, the *user in this function is useless
 */
int print_node_content(extTree *node, void *user, int depth){
  int n = depth * 2;
  IDT(n) std::cout << "node type: " ;
  dump_node_type_str(node->type);
  IDT(n) std::cout << "child_num: " << node->child_num;
  std::cout << "/ curr_stmt: " << node->curr_stmt << std::endl;
  if (node->type == isl_schedule_node_band){
    IDT(n) dump_ib(node->ib);
  }
  MemoryAccess *ar = NULL;
  if (node->type == isl_schedule_node_leaf){
    for (int i = 0; i < node->child_num; i++){
      ar = node->access_relations[i];
      // std::cout << ar->type << " " << ar->arrarName << " & ";
      if (ar->type != CONSTANT){
        char *str = isl_union_map_to_str(ar->access);
        IDT(n) std::cout << str;
        if (ar->type == READ) std::cout << " : read" << std::endl;
        else std::cout << " : write" << std::endl;
      } else {
        IDT(n) std::cout << "Constant access: " << ar->arrarName << " : read" << std::endl;
      }
    }
    return 0;
  }
  return 1;
}

extTree *calc_access_order(extTree *tree, void *user, int depth){
  dom_and_count *dc = (dom_and_count *)user;
  if(tree == NULL){
    return NULL;
  }
  domainSpace *dom = dc->dom;
  stmtSpace *stmt = NULL;
  indexBound *ib = NULL;
  isl_union_set *lexmin = NULL;
  int iter_count = 0;
  int val = 0;
  switch (tree->type){
    case isl_schedule_node_band:
      val = tree->ib->ub_val - tree->ib->lb_val + 1;
      std::cout << "BandVal: " << val << std::endl;
      dc->curr_access->top() = dc->curr_access->top() * val;
      break;
    case isl_schedule_node_leaf:
      dc->curr_access->push(0);
      for (int i = 0; i < tree->child_num; i++){
        MemoryAccess *ma = tree->access_relations[i];
        // find the corresponding ArrayRef from the map
        ArrayRef *ar = dom->array_refs->at(ma->arrarName);
        if (ma->type != CONSTANT && ar->first_access == NULL){
          ar->first_access = isl_union_map_copy(ma->access);
          // let me see the first access ??
          char *str = isl_union_map_to_str(ar->first_access);
          ar->first_occur = dc->curr_access->top();
          std::cout << "Array " << ma->arrarName << " first access at:  " << ar->first_occur << std::endl;
          stmt = find_stmt_from_domain(dom, tree->curr_stmt);
          lexmin = isl_union_set_lexmin(isl_union_set_copy(stmt->iter_space));
          // Will get sth like this: 
          // [tsteps, n] -> { S2[t, i, j] : t = 0 and i = 1 and j = 1 and tsteps > 0 and n >= 3 }
        } else if (ma->type == CONSTANT && ar->first_occur == 0) {
          ar->first_occur = dc->curr_access->top();
          std::cout << "Constant " << ma->arrarName << " first access at:  " << ar->first_occur << std::endl;
        }
        dc->curr_access->top() = dc->curr_access->top() + 1;
      }
      break;
    // case isl_schedule_node_filter:
    //   break;
    case isl_schedule_node_sequence:
      val = 0;
      iter_count = dc->curr_access->size();
      std::cout << "SequenceVal: " << dc->curr_access->size() << std::endl;
      for (int i = 0; i < iter_count; i++){
        std::cout << "Val: " << dc->curr_access->top() << std::endl;
        val += dc->curr_access->top();
        dc->curr_access->pop();
      }
      dc->curr_access->push(val);
      break;
    case isl_schedule_node_domain:
      std::cout << "Now val is: " << dc->curr_access->top() << std::endl;
      break;
    default:
      break;
  }
  return tree;
}

/*
 * Program initialization
 * argv[1]: the path to the binary
 * argv[2]: ppcg launch path
 */
int main(int argc, char *argv[]) {
  // initialize 10 ptr to store ppcg call path
  sim_prog_path = argv[1];
  exe_prog_path = argv[2];
  pet_prog_args = argv[3];
  int status = 0;

  /* 
   * int parse_dwarf(char **unit, FILE *fp)
   *
   * For launching the PPCG/pet to get the schedule/pet tree, 
   * Collect all file names that are needed to be included
   * from the dawrf of executable
   */
  FILE *fp;
  char cmd[BUFFER_SIZE];
  snprintf(cmd,BUFFER_SIZE-1, "readelf --debug-dump=info %s", sim_prog_path);
  fp = popen(cmd, "r");
  if (fp == NULL) {
      printf("Failed to run command\n");
      exit(1);
  }
  char *ret = (char *)(malloc(BUFFER_SIZE*sizeof(char) / 4));
  char **unit = (char **)(malloc(10 * sizeof(char *)));
  int compilation_unit = parse_dwarf(unit, fp);
  #ifdef DEBUG
  if (compilation_unit == 0) {
      printf("No DW_AT_name and DW_AT_comp_dir found\n");
  } else {
    // DEBUG
      printf("There are %d compilation unit\n", compilation_unit);
      for (int i = 0; i < compilation_unit; i++) {
          printf("%s\n", unit[i]);
      }
  }
  #endif
  /* 
   * int get_computed_sched_from_ppcg(char **unit, char *ret, int compilation_unit)
   *
   * Launch PPCG, get computed schedule, and reload it to the program later
   * We don't want a computed schedule for GPU, so we don't need the reschedule
   */
  int arg_count = get_computed_sched_from_ppcg(unit, ret, compilation_unit);
  if(!ret){
    printf("Error: ppcg call failed\n");
    return 1;
  }
  #ifdef DEBUG
  printf("The schedule is at %s\n", ret);
  #endif
  /*
   * int extract_dom_from_sched(FILE *file, domainSpace *dom)
   *
   * From schedule computed from PPCG, extract the domain of each statement 
   * and the iteration space of each statement (constraints) 
   * We may extract this part to another program later 
   * 
   * TODO: The ub/lb var is not very neat, some case the blank space is remained
   */
  isl_ctx *ctx;
  isl_schedule *schedule;
	ctx = isl_ctx_alloc();
  FILE *file;
	file = fopen(ret, "r");
	if (!file) {
		fprintf(stderr, "Unable to open '%s' for reading\n", ret);
		return 1;
	}
  domainSpace *dom = init_domainSpace();
  status = extract_dom_from_sched(file, dom);
  /* 
   * int parse_dwarf_calc_bound(FILE *fp, domainSpace *dom)
   * 
   * For variable like N, which is the index bound var,
   * that we can know before the execution. 
   * Find the acutal value from dwarf, reparse the dwarf  
   */
  fp = popen(cmd, "r");
  status = parse_dwarf_calc_bound(fp, dom);
  #ifdef DEBUG  
  for (auto p : var_n_val) {
    std::cout << p.first << " : " << p.second << "| ";
  } std::cout << std::endl;
  #endif
  /* 
   * int calc_dom_bound(domainSpace *dom)
   *
   * Use found vars to calculate the actual value of the variable
   * The ub_val and lb_val will bound the iteration space in such form:
   *                lb <= var <= ub , 0 <= lb <= ub
   * if there is unknown value, e.g. bounded by parent band node, lb/ub_val = -1
   * We could only know it until the execution. 
   */
  status = calc_dom_bound(dom);
  #ifdef DEBUG
  for (int i = 0; i < dom->stmt_num; i++) {
    stmtSpace *stmt = dom->stmt[i];
    std::cout << "S" << stmt->stmt_no << std::endl;
    for (int j = 0; j < stmt->ib_num; j++) {
      indexBound *ib = stmt->ib[j];
      dump_ib(ib);
    }
  }
  #endif
  /* 
   * int get_access_relation_from_pet(accessPerStmt *mem_access, char **unit, int compilation_unit)
   *
   * From pet tree, collect the data we needed for the program
   * Arrays, access relation, and prepare for 1st access
   */
  accessPerStmt *mem_access;
  mem_access = new accessPerStmt();
  dom->mem_access = mem_access;
  status = get_access_relation_from_pet(dom, mem_access, unit, compilation_unit);
  std::cout << "mem_access size: " << mem_access->size() << std::endl;
  #ifdef DEBUG
  char *dump_str;
  for(auto v : *mem_access){
      std::cout << "S" << v->first << std::endl;
      for(auto m : *v->second){
          std::cout << m->arrarName << " " << m->type << std::endl;
          if(m->type != accessType::CONSTANT){
              dump_str = isl_union_map_to_str(m->access);
              std::cout << dump_str << std::endl;
              free(dump_str);
          }
      }
  }

  std::cout << "ArrayRefs: " << std::endl;
  for (auto v : *dom->array_refs){
    std::cout << v.first << std::endl;
  }
  #endif
  /* 
   * int construction(isl_schedule_node *node, void *user)
   *
   * Construct the tree structure from the schedule tree
   * The tree structure is used to store the schedule tree
   * and the access relation of each statement
   */
  file = fopen(ret, "r");
  extTree *tree = init_extTree(dom, NULL);
  tree->child_num = 0;
  tree->type = isl_schedule_node_domain;
	schedule = isl_schedule_read_from_file(ctx, file);
  /* ExtTree Construction with callback function construction() ... */
  isl_stat stat_ret = isl_schedule_foreach_schedule_node_top_down(schedule,
						&construction, &tree);
  /* Back to tree head */
  while (tree->parent != NULL) {
    tree = tree->parent;
  }
  /* 
   * int extTree_preorder_traverse(extTree *tree, int (*fn)(extTree *node, void *user, int depth), void *user, int depth)
   * int print_node_content(extTree *node, void *user, int depth)
   * 
   * A callback function to traverse the tree, provide the depth additionally
   * The print_node_content is a callback function to print the content of the node,
   * which stop at leaf node. 
   * 
   * This indnet is useless actually ... ( The int indent = 0; )
   * However for full functionality support we preserve it
   */ 
  int indent = 0;
  dom_and_count *user= init_dom_and_count(dom);
  extTree *traverse =  extTree_postorder_traverse (tree->children[0], &calc_access_order, user, 0);
  // extTree_preorder_traverse (tree, &print_node_content, &user, 0);
  // dump the unordered map array ref from the domainSpace

  if (status == 1)
  {
    printf("Error: Unable to extract domain from the schedule\n");
    return 1;
  }

    /**********************************************/
   /*          End of collecting data            */
  /**********************************************/

  // Create data structure for collecting address
  /* Parse data may look like this: 
    ##### (after 5 #s)
    read: [tsteps, n, b0, b1] -> { S1[t, i, j] -> A[i, j] }
    read: [tsteps, n, b0, b1] -> { S1[t, i, j] -> A[i, -1 + j] }
    read: [tsteps, n, b0, b1] -> { S1[t, i, j] -> A[i, 1 + j] }
    read: [tsteps, n, b0, b1] -> { S1[t, i, j] -> A[1 + i, j] }
    read: [tsteps, n, b0, b1] -> { S1[t, i, j] -> A[-1 + i, j] }
    write: [tsteps, n, b0, b1] -> { S1[t, i, j] -> B[i, j] }
    write: [tsteps, n, b0, b1] -> { S2[t, i, j] -> A[i, j] }
    read: [tsteps, n, b0, b1] -> { S2[t, i, j] -> B[i, j] }
    read: [tsteps, n, b0, b1] -> { S2[t, i, j] -> B[i, -1 + j] }
    read: [tsteps, n, b0, b1] -> { S2[t, i, j] -> B[i, 1 + j] }
    read: [tsteps, n, b0, b1] -> { S2[t, i, j] -> B[1 + i, j] }
    read: [tsteps, n, b0, b1] -> { S2[t, i, j] -> B[-1 + i, j] }
  */
  int stmt = 1;
  // Read from the file after ##### occurs
  
  // Create pipe descriptors
  int pipe_fd[2];
  if (pipe(pipe_fd) == -1) {
    perror("pipe");
    exit(EXIT_FAILURE);
  }
  /*                  Extracttion                  */

    /**********************************************/
   /*                Call valgrind               */
  /**********************************************/

  // Fork a child process
  pid_t pid = fork();
  if (pid == -1) {
    perror("fork");
    exit(EXIT_FAILURE);
  }

  if (pid == 0) { // Child process (Program A)
    // Close the read end of the pipe
    close(pipe_fd[0]);

    // Redirect stdout to the pipe
  // It's magic, read from STDOUT and use VG_(message)(Vg_ClientMsg ... ) can send to the pipe
    dup2(pipe_fd[1], STDOUT_FILENO);

    // Close unused pipe descriptors
    close(pipe_fd[1]);

    // Change the working directory
    if (chdir("/home/dreyex/Documents/Research/PPT") == 0) {
      printf("Changed directory to /path/to/new_directory\n");
    } else {
      perror("chdir() error");
      return 1;
    }

    // Execute Program A
    // Since pass the program by arvg is sophisticated, we use execl with fixed path instead
    // What if then we have to run the batch of benchmarks?
    execl("/home/dreyex/Documents/Research/PPT/./vg-in-place", "vg-in-place",
          "--tool=cachegrind", "--instr-at-start=no", "--cache-sim=yes",
          "--D1=49152,12,64", "--I1=32768,8,64", "--L2=1310720,10,64", "-v", 
          "--log-fd=1", sim_prog_path, NULL);
    perror("execl");
    exit(EXIT_FAILURE);
  } else { // Parent process (Program B)
    // Close the write end of the pipe
    int counter = 0;
    close(pipe_fd[1]);

    // Read from the pipe continuously
    char buffer[BUFFER_SIZE];
    ssize_t bytes_read;
    char cache[BUFFER_SIZE * 2]; // Double the buffer size for caching
    size_t cache_index = 0;
    int stop_receiving = 0;
    while (!stop_receiving &&
           (bytes_read = read(pipe_fd[0], buffer, BUFFER_SIZE)) > 0) {
      // Check if caching the data would exceed the buffer size
      if (cache_index + bytes_read >= sizeof(cache)) {
        fprintf(stderr, "Error: Buffer overflow\n");
        exit(EXIT_FAILURE);
      }

      // Cache the received data
      memcpy(cache + cache_index, buffer, bytes_read);
      cache_index += bytes_read;

      // Check if there is a complete line in the cache
      char *line_start = cache;
      char *line_end;
      char access;
      int line_no, size;
      long long int addr;
      /*
       * Recording the address, add thme into polyhedral model
       * Why we still need to record? 
       * Since sometimes the address is not that continuous as what we thought
       * physical address may change the page instead ( just an assumption )
       */
      while ((line_end = strchr(line_start, '\n')) != NULL) {
        // Null-terminate the line
        *line_end = '\0';

        // Check if the line starts with '%'
        if (line_start[0] == '*') {
          // Output the line
          // printf("detected at %s\n", line_start);
          sscanf(line_start, "**%*d** %c %d %llx %d", &access, &line_no, &addr, &size);

          // Output parsed values
          // printf("Access: %c, Line No: %d, Address: 0x%.10llx, Size: %d\n", access, line_no, addr, size);
    
          counter++;
        }

        // Check if the line starts with '#', then stop receiving
        if (line_start[0] == '#') {
          stop_receiving = 1;
          break;
        }

        // Move to the next line
        line_start = line_end + 1;
      }

      // Move the remaining data to the beginning of the cache
      size_t remaining_bytes = cache_index - (line_start - cache);
      memmove(cache, line_start, remaining_bytes);
      cache_index = remaining_bytes;
    }
    printf("There are %d line of output to here\n", counter);

    // Close the read end of the pipe
    close(pipe_fd[0]);

    // Wait for the child process to finish
    int status;
    waitpid(pid, &status, 0);
  }

  // Free the array of ptr
  for (int i = 0; i < compilation_unit; i++) {
    free(unit[i]);
  }
  free(unit);
	fclose(file);
  isl_schedule_free(schedule);
  isl_ctx_free(ctx);
  free(ret);
  return 0;
}
