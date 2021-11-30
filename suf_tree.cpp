/*
This work is done by 
Rubayet Rahman Rongon
& 
Kazi Misba Ul Islam
as a project implementation of paper "On Shortest Unique Substring Queries"

*/
#include <iostream>
#include <iomanip>
#include <cstdlib>
#include <string.h>
#include <cassert>
#include <string>
#include <vector>
#include <map>
#include <fstream>

using std::cout;
using std::cin;
using std::cerr;
using std::setw;
using std::flush;
using std::endl;

const int NO_MATCH=0;
const int PARTIAL_MATCH=1;
const int FULL_MATCH=2;
const bool DEBUG_LOG = true;

const int CASE_1 = 1;
const int CASE_2 = 2;
const int CASE_3 = 3;
const int CASE_4 = 4;

void map_leaf_pos();
int find_leaf_node(std::string search_string, int pos);
void find_lsus();
void baseline_algorithm();
void unique_substring();
void find_MUS();
void preComputation_algorithm();
bool check_if_MUS(int l, int r);
void propagate(int start, int end, int k);


class data_box{
    public:
        int start_node;
        int end_node;
        int suffix_node;
        int first_char_index;
        int last_char_index;

        std::string substring;

        data_box(int start_node,
        int end_node,
        int suffix_node,
        int first_char_index,
        int last_char_index,
        std::string substring);
};

data_box::data_box(int start_node_l,
        int end_node_l,
        int suffix_node_l,
        int first_char_index_l,
        int last_char_index_l,
        std::string substring_l){
    
    start_node = start_node_l;
    end_node = end_node_l;
    suffix_node = suffix_node_l;
    first_char_index = first_char_index_l;
    last_char_index = last_char_index_l;
    substring = substring_l;

}
//
// The maximum input string length this program
// will handle is defined here.  A suffix tree
// can have as many as 2N edges/nodes.  The edges
// are stored in a hash table, whose size is also
// defined here.
//
const int MAX_LENGTH = 100000;
const int HASH_TABLE_SIZE = 217999;  //A prime roughly 10% larger

//
// The input buffer and character count.  Please note that N
// is the length of the input string -1, which means it
// denotes the maximum index in the input buffer.
//

char T[ MAX_LENGTH ];
char tt[ MAX_LENGTH ];
int N;

struct Baseline_sus{
    int start_pos;
    int end_pos;
};

struct Candidate{
    int i;
    int j;
};

struct Algo3_candidate{
    std::string cand;
    int start;
    int end;
};

/* storage variables */
std::vector<data_box> DATA_HUB;
std::map<int, int> _POS_LEAF_MAPPING;
std::map<int, int> _POS_EDGE_LEN_MAPPING;
std::map<int, std::string> _LSUS;
int * _lsus_size = new int [N];
std::map<int, Baseline_sus> _BASELINE_SUS;
std::map<std::string, Candidate> _SUBSTRING_POS_MAPPING;
std::vector<Candidate> _UNIQUE_SUBSTRING_POS;
std::vector<Candidate> _MUS;
std::vector<Algo3_candidate> _Algo3_VECTOR;

class Suffix {
    public :
        int origin_node;
        int first_char_index;
        int last_char_index;
        Suffix( int node, int start, int stop )
            : origin_node( node ),
              first_char_index( start ),
              last_char_index( stop ){};
        int Explicit(){ return first_char_index > last_char_index; }
        int Implicit(){ return last_char_index >= first_char_index; }
        void Canonize();
};

//
// The suffix tree is made up of edges connecting nodes.
// Each edge represents a string of characters starting
// at first_char_index and ending at last_char_index.
// Edges can be inserted and removed from a hash table,
// based on the Hash() function defined here.  The hash
// table indicates an unused slot by setting the
// start_node value to -1.
//

class Edge {
    public :
        int first_char_index;
        int last_char_index;
        int end_node;
        int start_node;
        void Insert();
        void Remove();
        Edge();
        Edge( int init_first_char_index,
              int init_last_char_index,
              int parent_node );
        int SplitEdge( Suffix &s );
        static Edge Find( int node, int c );
        static int Hash( int node, int c );
};

/*
Each suffix tree is composed of nodes connected by edges.
So we have nodes class and edge class each having some capabilities as function
*/
class Node {
    public :
        int suffix_node;
        Node() { suffix_node = -1; }
        static int Count;
};

Edge Edges[ HASH_TABLE_SIZE ];

int Node::Count = 1;
Node Nodes[ MAX_LENGTH * 2 ];

Edge::Edge()
{
    start_node = -1;
}


Edge::Edge( int init_first, int init_last, int parent_node )
{
    first_char_index = init_first;
    last_char_index = init_last;
    start_node = parent_node;
    end_node = Node::Count++;
}

int Edge::Hash( int node, int c )
{
    return ( ( node << 8 ) + c ) % HASH_TABLE_SIZE;
}


void Edge::Insert()
{
    int i = Hash( start_node, T[ first_char_index ] );
    while ( Edges[ i ].start_node != -1 )
        i = ++i % HASH_TABLE_SIZE;
    Edges[ i ] = *this;
}

void Edge::Remove()
{
    int i = Hash( start_node, T[ first_char_index ] );
    while ( Edges[ i ].start_node != start_node ||
            Edges[ i ].first_char_index != first_char_index )
        i = ++i % HASH_TABLE_SIZE;
    for ( ; ; ) {
        Edges[ i ].start_node = -1;
        int j = i;
        for ( ; ; ) {
            i = ++i % HASH_TABLE_SIZE;
            if ( Edges[ i ].start_node == -1 )
                return;
            int r = Hash( Edges[ i ].start_node, T[ Edges[ i ].first_char_index ] );
            if ( i >= r && r > j )
                continue;
            if ( r > j && j > i )
                continue;
            if ( j > i && i >= r )
                continue;
            break;
        }
        Edges[ j ] = Edges[ i ];
    }
}

Edge Edge::Find( int node, int c )
{
    int i = Hash( node, c );
    for ( ; ; ) {
        if ( Edges[ i ].start_node == node )
            {
                if ( c == T[ Edges[ i ].first_char_index ] )
                    return Edges[ i ];
            }
            
        if ( Edges[ i ].start_node == -1 ){
            return Edges[ i ];
        }
            
        i = ++i % HASH_TABLE_SIZE;
    }
}

int Edge::SplitEdge( Suffix &s )
{
    Remove();
    Edge *new_edge =
      new Edge( first_char_index,
                first_char_index + s.last_char_index - s.first_char_index,
                s.origin_node );
    new_edge->Insert();
    Nodes[ new_edge->end_node ].suffix_node = s.origin_node;
    first_char_index += s.last_char_index - s.first_char_index + 1;
    start_node = new_edge->end_node;
    Insert();
    return new_edge->end_node;
}


void map_leaf_pos(){
    /*
    Store suffix string for  different positions
    and matching one by one to find the leaf edge 
    and leaf node.


    */
    const int SIZE = N+1;
    char substring_arr [SIZE];
    memset(substring_arr, 0, sizeof substring_arr);
    std::vector <std::string> substring_hub;
    
    for (int i=0; i<N; i++){
        int x = 0;
        for (int j=i; j<=N; j++){
            substring_arr[x] = T[j];
            x++;
        }
        substring_arr[x] = '\0';
        std::string substring(substring_arr);
        substring_hub.push_back(substring);
        memset(substring_arr, 0, sizeof substring_arr);
    }

    for (int i=0; i< substring_hub.size(); i++){
        //printf("%s\n", substring_hub[i].c_str());
        std::string search_string = substring_hub[i];
        int leaf_node = find_leaf_node(search_string, i);
        _POS_LEAF_MAPPING.insert(std::pair<int,int>(i,leaf_node)) ;
    }
}

int find_leaf_node(std::string search_string, int pos){
    /*
    find the leaf edge and leaf node.
    */
    int match_pos = 0;
    int end_node = -1;
    int matches = NO_MATCH;
    int next_node= -1;
    int final_end_node = -1;

    int intermediate_pos_increase = -1;
    
    for (int i=0; i< DATA_HUB.size(); i++){
        
        data_box data = DATA_HUB[i];
        std::string suffix_string = data.substring;
        int is_suffix = data.suffix_node;
        //cout << "current suffix string: " << suffix_string << endl;

        if (matches == NO_MATCH){
            next_node = data.end_node;
            
            int possible_partial_length = std::min(search_string.length() - match_pos, suffix_string.length());

            for (int j=0; j< possible_partial_length; j++){
                if(suffix_string[j]!= search_string[j+match_pos]){
                    matches = NO_MATCH;
                    intermediate_pos_increase = -1;
                    break;
                }else{
                    matches = PARTIAL_MATCH;
                    intermediate_pos_increase = j+1 ;
                }

                if (matches == PARTIAL_MATCH && match_pos == search_string.length()){
                    matches = FULL_MATCH;
                    break;
                }
            }
            
            if (matches == PARTIAL_MATCH){
                match_pos = match_pos + intermediate_pos_increase;
                i=0;
            }
            
            if(is_suffix==-1 && matches==PARTIAL_MATCH){
                break;
            }
            
        }else if(matches==PARTIAL_MATCH){
            // match the previous end node with current start node starting from very begining
            int current_start_node = data.start_node;

            if (current_start_node == next_node) {
                int possible_partial_length = std::min(search_string.length() - match_pos, suffix_string.length());

                for (int j=0; j< possible_partial_length; j++){
                    if(suffix_string[j]!= search_string[match_pos +j]){
                        matches = PARTIAL_MATCH;
                        intermediate_pos_increase = -1;
                        break;
                    }else{
                        matches = PARTIAL_MATCH;
                        next_node = data.end_node;
                        intermediate_pos_increase = j+1;
                    }
                }
                if(intermediate_pos_increase > -1){
                    match_pos = match_pos + intermediate_pos_increase;
                    i = 0;
                }
                if (matches == PARTIAL_MATCH && match_pos == search_string.length()){
                        matches = FULL_MATCH;
                        next_node = data.end_node;
                        end_node = data.end_node;
                        break;
                }
                
            }
        }
    }

    switch (matches)
    {
        case FULL_MATCH:
            // hold the last node
            // break
            // if (DEBUG_LOG)
            //     cout << "search string: " << search_string << " end node: " << end_node << ", leaf edge len: " << intermediate_pos_increase << endl;
            _POS_EDGE_LEN_MAPPING.insert(std::pair<int, int>(pos, intermediate_pos_increase-1));
            break;
        case NO_MATCH:
            end_node = -1;
            break;
        
        case PARTIAL_MATCH:
            if (match_pos == search_string.length()){
                // if (DEBUG_LOG)
                //     cout << "search string: " << search_string << " end node: " << end_node << ", leaf edge len: " << intermediate_pos_increase << endl;
            }
            _POS_EDGE_LEN_MAPPING.insert(std::pair<int, int>(pos, intermediate_pos_increase-1));
        default:
            break;
    }

    return end_node;
}

void find_lsus(){
    /*
    finding lsus
    */
    std::map<int, int >::iterator it;
    
    for (it=_POS_EDGE_LEN_MAPPING.begin(); it != _POS_EDGE_LEN_MAPPING.end(); it++) {
        int pos = it->first;
        int leaf_len = it->second;
        
        if (leaf_len >0){
            int end_pos = N-leaf_len;
            //lsus S[p, n-l+1]
            char *lsus = new char[end_pos-pos+1];
            int index = 0;
            for (int i=pos ; i<= end_pos ; i++){
                try{
                lsus[index]=T[i];
                index++;}
                catch(const std::exception& e){
                    lsus = "";
                }
            }
            
            if (DEBUG_LOG)
                cout << "lsus at pos: " << pos << " is: " << lsus << endl;
            _LSUS.insert(std::pair<int, std::string>(pos, lsus));
            _lsus_size[pos] = end_pos;
        }else {
            std::string null_string = "";
            _LSUS.insert(std::pair<int, std::string>(pos, null_string));
            _lsus_size[pos] = N;
        }
         
    }
}

void baseline_algorithm(){
    // output: leftmost SUS containing position p
    std::map<int, std::string >::iterator it;
    int i,j;
    cout << "---BASELINE----" << endl;
    for (it=_LSUS.begin(); it != _LSUS.end(); it++){
        int pos = it->first;
        std::string lsus = it->second;
        
        if (lsus == "" ){
            it->second = T;
            _lsus_size[pos] = N;
        }
        if (DEBUG_LOG)
            cout << "pos: " << pos <<  ", lsus: " << it->second << endl;
        
        i = pos;
        j = _lsus_size[pos];
        
        for (int k= pos-1; k>= 0 && pos-k <= j-i; k--){
            if (_lsus_size[k]==N)
                continue;
            
            int r = _lsus_size[k];
            
            if(r<pos)
                r = pos;
            if(r-k<=j-i){
                i=r;
                j=k;
            }
        }
        
        if (i>j){
            int temp = j;
            j=i;
            i=temp;
        }
        
        Baseline_sus b_sus;
        b_sus.start_pos = i;
        b_sus.end_pos=j;
        
        char *baseline_lsus = new char[j-i+1];
        int index = 0;
        for (int x=i ; x<= j ; x++){
            baseline_lsus[index]=T[x];
            index++;
        }
        
        cout << "pos: "<< pos << ", start pos: " << i << ", endpos: " << j << ", lsus: " << baseline_lsus <<  endl;
        _BASELINE_SUS.insert(std::pair<int, Baseline_sus>(pos, b_sus));
    }
    
}

void unique_substring(){
    /*
    For finding uniqueu substring from string.
    Part of finding MUS
    */
    std::string full_string(T);
    
    std::vector<std::string> a1;
    for (int i = 0; i < full_string.size(); i++)
    {
        for (int j = i + 1; j < full_string.size(); j++)
        {
            // Avoid multiple occurences
            if (i != j){
                // Append all substrings
                std::string substring = full_string.substr(i,j+1);
                a1.push_back(substring);
                
                Candidate c;
                c.i = i;
                c.j = j+1;
                _SUBSTRING_POS_MAPPING.insert(std::pair<std::string, Candidate>(substring, c));
                
            }
        }
    }
    
    // all the substrings
    std::map<std::string,int> a2;
    for(std::string i:a1) a2[i]++;
    
    std::vector<std::string> freshlist;
    
    for (auto i:a2)
    {
 
          // If frequency is 1
        if (i.second == 1){
            // Append into fresh list
            std::string unique_string = i.first;
            freshlist.push_back(unique_string);
            
            //cout << "unique substring: " << unique_string << endl;
            
            std::map<std::string, Candidate>::iterator it;
            
            for (it=_SUBSTRING_POS_MAPPING.begin(); it != _SUBSTRING_POS_MAPPING.end(); it++) {
                std::string substring = it->first;
                Candidate str_pos = it->second;
                
                if (substring==unique_string){
                    _UNIQUE_SUBSTRING_POS.push_back(str_pos);
                }
            }
        }
    }
}

void find_MUS(){
    /*
    check if the uniue substring is actually MUS
    */
    for(int i=0;i<_UNIQUE_SUBSTRING_POS.size();i++){
        Candidate c = _UNIQUE_SUBSTRING_POS[i];
        Candidate true_c;
        int candidate_i = c.i;
        int candidate_j = c.j;
        
        bool is_mus = false;
        true_c = c;
        
        for (int j=0; j< _UNIQUE_SUBSTRING_POS.size(); j++){
            Candidate c_prime = _UNIQUE_SUBSTRING_POS[j];
            
            int i_prime = c_prime.i;
            int j_prime = c_prime.j;
            
            if( i_prime>candidate_i && j_prime < candidate_j){
                is_mus = false;
                break;
            }else{
                is_mus = true;
            }
        }
        
        if(is_mus){
            _MUS.push_back(true_c);
            
            if (DEBUG_LOG)
                cout << "true mus i: " << true_c.i << ", j: "<< true_c.j << endl;
        }
    }
}

void preComputation_algorithm(){
    /*
    This is extension of algorithm 1 where we just calculated lsus.
    Now need to find SUS using lsus. Our precomputation goal is to calculate this part as a precomputation.
    So the we can make log(1) time query for any position SUS.
    */
    for(int i=0;i< N; i++){
        Algo3_candidate alg3_cand;
        alg3_cand.start = -1;
        alg3_cand.end = -1;
        alg3_cand.cand = "";
        
        _Algo3_VECTOR.push_back(alg3_cand);
    }
    
    int i= 0;
    int j = _lsus_size[0];
    int i_prev = 0;
    int j_prev = j;
    
    _Algo3_VECTOR[0].end = j;
    _Algo3_VECTOR[0].start = i;
    char * _smallest_string = new char[j-i+1];
    int index=0;
    for(int m=i; m <= j ; m++){
        _smallest_string[index] = T[m];
        index++;
    }
    _Algo3_VECTOR[0].cand = _smallest_string;
    
    int case_own = -1;
    
    for(int pos= 1; pos < N; pos++ ){
        int r = _lsus_size[pos];
        int l = pos;
        
        int candidate1 =999999999;
        int candidate2 =999999999;
        int candidate3 =999999999;
        int candidate4= 999999999;
        
        candidate1 = r-l+1;
        
        Algo3_candidate alg3_cand = _Algo3_VECTOR[pos];
        
        if(alg3_cand.cand != ""){

            
            candidate2 = int(alg3_cand.cand.length());
        }
        
        if (candidate1 < candidate2){
            case_own = CASE_1;
        }else if (candidate2 < candidate1){
            case_own = CASE_2;
        }else{
            if(alg3_cand.start < l ){
                case_own = CASE_2;
            }else{
                case_own = CASE_1;
            }
        }
        
        if(j_prev < pos){
            candidate3 = pos - i_prev + 1;
            
            if (case_own == CASE_1){
                if (candidate3 < candidate1){
                    case_own = CASE_3;
                }else{
                    case_own = CASE_1;
                }
            }else if (case_own == CASE_2){
                if (candidate3 < candidate2){
                    case_own = CASE_3;
                }else{
                    case_own = CASE_2;
                }
            }
        }
        
        candidate4 = j_prev - i_prev + 1;
        if(case_own == 1){
            if(candidate4 < candidate1 ){
                case_own = CASE_4;
            }else{
                case_own = CASE_1;
            }
        }else if (case_own == 2){
            if(candidate4 < candidate2){
                case_own = CASE_4;
            }else{
                case_own = CASE_2;
            }
        }else if (case_own == 3){
            if(candidate4 < candidate3){
                case_own = 4;
            }else{
                case_own = CASE_3;
            }
        }
        
        switch (case_own) {
            case CASE_1:
                i = l;
                j = r;
                break;
            case CASE_2:
                i = alg3_cand.start;
                j = alg3_cand.end;
                break;
            case CASE_3:
                i = i_prev;
                j= pos;
                break;
            case CASE_4:
                i = i_prev;
                j= j_prev;
                break;
            default:
                break;
        }
        
        Algo3_candidate smallest_candidate;
        
        if (j<i){
            int temp = j;
            j=i;
            i=temp;
        }else if (i==-1 || j==-1){
            i=1;
            j=2;
        }
        
        char * _smallest_string = new char[j-i+1];
        int index=0;
        for(int m=i; m <= j ; m++){
            _smallest_string[index] = T[m];
            index++;
        }
        
        int x = -1;
        int y = -1;
        if (alg3_cand.cand != ""){
            x = alg3_cand.start;
            y = alg3_cand.end;
        }
        
        bool is_in_MUS = false;
        is_in_MUS = check_if_MUS(l,r);
        
        if (alg3_cand.cand != "" && y>j){
            propagate(x, y, j+1);
        }else if (is_in_MUS && r>j && !(i==l && r==j)){
            propagate(l, r, j+1);
        }
        
        i_prev = i;
        j_prev = j;
    }
    
    for (int pos=0 ; pos < _Algo3_VECTOR.size(); pos++){
        if (_Algo3_VECTOR[pos].cand==""){
            int s = _lsus_size[pos];
            char * _cand = new char[s-pos+1];
            int index=0;
            for(int m=pos; m <= s ; m++){
                _cand[index] = T[m];
                index++;
            }
            _Algo3_VECTOR[pos].cand = _cand;
            _Algo3_VECTOR[pos].start = pos;
            _Algo3_VECTOR[pos].end = s;
        }
        
        cout << "SUS at position: " << pos << " : " << _Algo3_VECTOR[pos].cand << ", length: " <<  _Algo3_VECTOR[pos].cand.length()<< endl;
    }
}

bool check_if_MUS(int l, int r){
    /*
    While finding SUS is algorithm 3 we need to check if a lsus is MUS or not for
    a specific condition. This function takes lsus position as input and matches all 
    calculated MUS with it.
    */
    bool is_mus = false;
    for(int i=0; i< _MUS.size(); i++){
        Candidate mus = _MUS[i];
        int mus_i = mus.i;
        int mus_j = mus.j;
        
        if (l==mus_i && r==mus_j){
            is_mus = true;
        }
    }
    return is_mus;
}

void propagate(int i, int j, int k){
    /*
    For efficient propagation of the  algorithm 3 this function is used.
    It checkes if a more eligible candidate covers up up to it's possible next positions then
    less eligible sus will carry forward to other position to compete. Thus, any less optimal
    SUS does not vanish from the competition just for losing at any certain position.
    */
    
    Algo3_candidate k_candidate = _Algo3_VECTOR[k];
    
    if(k < i || k>j)
        return;
    else if (k_candidate.cand == ""){
        k_candidate.start = i;
        k_candidate.end = j;
        
        char * _cand = new char[j-i+1];
        int index=0;
        for(int m=i; m <= j ; m++){
            _cand[index] = T[m];
            index++;
        }
        k_candidate.cand = _cand;
        
        _Algo3_VECTOR[k] = k_candidate;
        return;
    }
    
    int i_prime = k_candidate.start;
    int j_prime = k_candidate.end;
    
    if ((j_prime - i_prime) > j-i) {
        char * _cand = new char[j-i+1];
        int index=0;
        for(int m=i; m <= j ; m++){
            _cand[index] = T[m];
            index++;
        }
        k_candidate.cand = _cand;
        k_candidate.start=i;
        k_candidate.end = j;
        
        _Algo3_VECTOR[k] = k_candidate;
        
        if (j_prime > j ){
            propagate(i_prime, j_prime, j+1);
        }
    }else if (((j_prime-i_prime) < (j-i) ) && (j_prime<j) ){
        propagate(i, j, j_prime+1);
    }else{
        if(i<i_prime){
            char * _cand = new char[j-i+1];
            int index=0;
            for(int m=i; m <= j ; m++){
                _cand[index] = T[m];
                index++;
            }
            k_candidate.cand = _cand;
            k_candidate.start = i;
            k_candidate.end = j;
            
            _Algo3_VECTOR[k] = k_candidate;
            propagate(i_prime, j_prime, j_prime+1);
        }else{
            propagate(i, j, j_prime+1);
        }
        
        return;
    }
}

void dump_edges( int current_n )
{
    for ( int j = 0 ; j < HASH_TABLE_SIZE ; j++ ) {
        Edge *s = Edges + j;
        if ( s->start_node == -1 )
            continue;
        int start_node = s->start_node;
        int end_node =  s->end_node;
        int suffix_node = Nodes[ s->end_node ].suffix_node;
        int first_char_index = s->first_char_index;
        int last_char_index = s->last_char_index;

        int top;
        if ( current_n > s->last_char_index )
            top = s->last_char_index;
        else
            top = current_n;
        std::string substring;
        for ( int l = s->first_char_index ;
                  l <= top;
                  l++ ){
                      substring += T[l];
                      //cout << T[ l ];
                  }
            
        data_box data (start_node, end_node, suffix_node, first_char_index, last_char_index, substring);
        DATA_HUB.push_back(data);
        // cout << "\n";
    }
}

//
// A suffix in the tree is denoted by a Suffix structure
// that denotes its last character.  The canonical
// representation of a suffix for this algorithm requires
// that the origin_node by the closest node to the end
// of the tree.  To force this to be true, we have to
// slide down every edge in our current path until we
// reach the final node.

void Suffix::Canonize()
{
    if ( !Explicit() ) {
        Edge edge = Edge::Find( origin_node, T[ first_char_index ] );
        int edge_span = edge.last_char_index - edge.first_char_index;
        while ( edge_span <= ( last_char_index - first_char_index ) ) {
            first_char_index = first_char_index + edge_span + 1;
            origin_node = edge.end_node;
            if ( first_char_index <= last_char_index ) {
               edge = Edge::Find( edge.end_node, T[ first_char_index ] );
                edge_span = edge.last_char_index - edge.first_char_index;
            };
        }
    }
}

void AddPrefix( Suffix &active, int last_char_index ) // origin_node=0, first_char=0, last_char=-1
{
    int parent_node;
    int last_parent_node = -1;

    for ( ; ; ) {
        Edge edge;
        parent_node = active.origin_node;
//
// Step 1 is to try and find a matching edge for the given node.
// If a matching edge exists, we are done adding edges, so we break
// out of this big loop.
//
        if ( active.Explicit() ) {
            edge = Edge::Find( active.origin_node, T[ last_char_index ] );
            if ( edge.start_node != -1 )
                break;
        } else { //implicit node, a little more complicated
            edge = Edge::Find( active.origin_node, T[ active.first_char_index ] );
            int span = active.last_char_index - active.first_char_index;
            if ( T[ edge.first_char_index + span + 1 ] == T[ last_char_index ] )
                break;
            parent_node = edge.SplitEdge( active );
        }
//
// We didn't find a matching edge, so we create a new one, add
// it to the tree at the parent node position, and insert it
// into the hash table.  When we create a new node, it also
// means we need to create a suffix link to the new node from
// the last node we visited.
//
        Edge *new_edge = new Edge( last_char_index, N, parent_node );
        new_edge->Insert();
        if ( last_parent_node > 0 )
            Nodes[ last_parent_node ].suffix_node = parent_node;
        last_parent_node = parent_node;
//
// This final step is where we move to the next smaller suffix
//
        if ( active.origin_node == 0 )
            active.first_char_index++;
        else
            active.origin_node = Nodes[ active.origin_node ].suffix_node;
        active.Canonize();
    }
    if ( last_parent_node > 0 )
        Nodes[ last_parent_node ].suffix_node = parent_node;
    active.last_char_index++;  //Now the endpoint is the next active point
    active.Canonize();
};

int main()
{

    // std::string str = "/Users/rubayetrahmanrongon/Desktop/sample_dna.txt";
    // std::ifstream is(str);     // open file

    // char c;
    // int ind=0;
    // while (is.get(c)){
    //     T[ind] = c;
    //     ind++;
    // }
    // T[ind] = '\0';
    // //cin.getline( T, MAX_LENGTH - 1 );
    // //N = strlen( T ) - 1;
    // N=ind-1;

    cout << "Enter string: " << flush;
    cin.getline( T, MAX_LENGTH - 1 );
    N = strlen( T ) - 1;

    Suffix active( 0, 0, -1 );  // The initial active prefix
    for ( int i = 0 ; i <= N ; i++ )
        AddPrefix( active, i );

    /* Added by
     @rubayet */
    
    dump_edges( N );
    map_leaf_pos();
    find_lsus();
    baseline_algorithm();
    unique_substring();
    find_MUS();
    preComputation_algorithm();
    
    std::string search_string;
    std::string X(T);
    cout << "Enter string you want to find SUS for: " << flush;
    
    while (std::getline(std::cin, search_string))
    {
        if(search_string=="q" || search_string=="Q")
            exit(1);
        std::size_t found = X.find(search_string);
        
        std::vector<size_t> positions; // holds all the positions that sub occurs within str

        std::size_t pos = X.find(search_string, 0);
        while(pos != std::string::npos)
        {
            positions.push_back(pos);
            pos = X.find(search_string,pos+1);
        }
        
        for (int i=0; i< positions.size();i++){
            std::string sus = _Algo3_VECTOR[positions[i]].cand;
            cout << "SUS found at position: " << positions[i] << ", is: " << sus << endl;
        }
    }
    
    return 1;
};

char CurrentString[ MAX_LENGTH ];
char GoodSuffixes[ MAX_LENGTH ];
char BranchCount[ MAX_LENGTH * 2 ] = { 0 };

/*
I, Rubayet and Kazi For suffix tree basics and implementation of suffix tree 
took help from this website https://marknelson.us/posts/1996/08/01/suffix-trees.html
titled as "Fast String Searching With Suffix Trees" by Mark Nelson.
*/