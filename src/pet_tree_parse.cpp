#include <bits/stdc++.h>
#include <isl/ctx.h>
#include <isl/options.h>
#include <isl/set.h>
#include <isl/space.h>
#include <isl/union_map.h>
#include <isl/union_set.h>

using namespace std;
#define MAX_BUF 1000

typedef  std::uint64_t hash_t;  
   
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

// Struct for memory access
typedef struct{
    int indent;
    int lineno;
    string arrarName;
    accessType type;
    isl_union_map *access;
} MemoryAccess;

std::string extractRefName(const std::string& str) {
  // Find positions of '->' and '['
  size_t start_pos = str.find("->");
  size_t end_pos = str.find("[");

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


int main(){
    // Open the file with pet tree
    ifstream file("/home/dreyex/Documents/Research/PPT/log_file/pet_tree.log");
    // Open the source code and find where the statement is
    // Will in such form: S%d: ... (the statements, with tag starting with S%d)
    ifstream source("/home/dreyex/Documents/Research/TraceBench/./stencils/jacobi-2d/jacobi-2d.c");
    string line;
    vector<string> pet_tree;
    vector<string> source_code;
    // A hash map for S1 to Sn
    vector<pair<int, vector<MemoryAccess *> *> *> mem_access;
    isl_ctx *ctx = isl_ctx_alloc();
    
    if(!file.is_open()){
        cout << "Error opening file pet" << endl;
        return 1;
    }
    while(getline(file, line)){
        pet_tree.push_back(line);
    }
    if(!source.is_open()){
        cout << "Error opening file source" << endl;
        return 1;
    }
    while(getline(source, line)){
        source_code.push_back(line);
    }

    vector<pair<int, int> *> pet_tree_tag = {};
    pair<int, int> *p;

    // Find the statement in the source code
    for(int i = 0; i < source_code.size(); i++){
        if(source_code[i][0] == 'S'){
            int stmt;
            string tag = source_code[i].substr(0, 2);
            sscanf(tag.c_str(), "S%d:", &stmt);
            // pet_tree_tag.push_back(make_pair(stmt, i+1));
            p = new pair<int, int>(stmt, i+1);
            pet_tree_tag.push_back(p);
        }
    }


    int cur_line = 0;
    int stmt;
    int i = 0;
    for (i; i < pet_tree.size(); i++){
        if(pet_tree[i] == "statements:")
            break;
    }
    int found = 0;
    char op[MAX_BUF] = {0};
    // From now on only "- line" starts at the beginning of the line
    for(i ; i < pet_tree.size();i++){
        // cout << pet_tree[i] << endl;
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
            pair<int, vector<MemoryAccess *> *> *maPair = new pair<int, vector<MemoryAccess *> *>();
            vector<MemoryAccess *> *list = new vector<MemoryAccess *>();
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
                    if(pet_tree[i].find("type") != string::npos){
                        break;
                    }
                }
                // Get the type of the statement
                // For example: "    type: expression" -> "expression"
                char type[20]; // Adjust size based on your needs
                char expression[100]; // Adjust size based on your needs
                char access[MAX_BUF]; // Adjust size based on your needs

                // Skip leading whitespace using "%*s"
                sscanf(pet_tree[i].c_str(), "%*s%*[:]");

                // Read "type:" and the expression
                sscanf(pet_tree[i].c_str(), "%[^:]%*[: ]%s", type, expression);

                // printf("type:%s at %d\n", type, i);
                MemoryAccess *mem;
                isl_union_map *union_map;
                auto str = pet_tree[i];
                std::string::iterator colon_pos;
                std::string s(type);
                size_t start_pos;
                size_t end_pos;
                std::string extracted_part;
                mem = new MemoryAccess();
                mem->indent = s.find("- type");
                mem->lineno = i;
                int is_read = 0;

                switch(hash_(expression)){
                    case  hash_compile_time( "access" ): 
                        // cout << "Access" << endl;
                        i++;
                        // get the union map of access, find the first pos of ':'
                        str = pet_tree[i];
                        start_pos = str.find("{");
                        end_pos = str.find("}");
                        extracted_part = str.substr(start_pos, end_pos - start_pos+1);
                        // cout << "Access: " << extracted_part << endl;
                        union_map = isl_union_map_read_from_str(ctx, extracted_part.c_str());
                        mem->access = union_map;
                        mem->arrarName = extractRefName(extracted_part);
                        i+=2;
                        str = pet_tree[i];
                        sscanf(pet_tree[i].c_str(), "%[^:]%*[: ]%d", type, &is_read);
                        mem->type = is_read ? READ : WRITE;
                        maPair->second->push_back(mem);
                        
                        break;
                    case  hash_compile_time( "double" ): 
                        // cout << "Double" << endl;
                        mem->type = CONSTANT;
                        i++;
                        sscanf(pet_tree[i].c_str(), "%[^:]%*[: ]%s", type, expression);
                        mem->arrarName = expression;
                        maPair->second->push_back(mem);
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
            mem_access.push_back(maPair);
        }
    }

    // Dump out all pair to check
    for(auto v : mem_access){
        cout << "S" << v->first << endl;
        for(auto m : *v->second){
            cout << m->arrarName << " " << m->type << endl;
            if(m->type != accessType::CONSTANT)
                isl_union_map_dump(m->access);
        }
    }
}