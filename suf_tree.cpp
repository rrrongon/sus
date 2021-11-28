//
// STREE2006.CPP - Suffix tree creation
//
// Mark Nelson, updated December, 2006
//
// This code has been tested with Borland C++ and
// Microsoft Visual C++.
//
// This program asks you for a line of input, then
// creates the suffix tree corresponding to the given
// text. Additional code is provided to validate the
// resulting tree after creation.
//
#include <iostream>
#include <iomanip>
#include <cstdlib>
#include <string.h>
#include <cassert>
#include <string>
#include <vector>
#include <map>

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

void map_leaf_pos();
int find_leaf_node(std::string search_string, int pos);
void find_lsus();
void baseline_algorithm();
void unique_substring();
void find_MUS();

void propagate(int start, int end, int k);
//
// When a new tree is added to the table, we step
// through all the currently defined suffixes from
// the active point to the end point.  This structure
// defines a Suffix by its final character.
// In the canonical representation, we define that last
// character by starting at a node in the tree, and
// following a string of characters, represented by
// first_char_index and last_char_index.  The two indices
// point into the input string.  Note that if a suffix
// ends at a node, there are no additional characters
// needed to characterize its last character position.
// When this is the case, we say the node is Explicit,
// and set first_char_index > last_char_index to flag
// that.
//

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
const int MAX_LENGTH = 1000;
const int HASH_TABLE_SIZE = 2179;  //A prime roughly 10% larger

//
// The input buffer and character count.  Please note that N
// is the length of the input string -1, which means it
// denotes the maximum index in the input buffer.
//

char T[ MAX_LENGTH ];
int N;

struct Baseline_sus{
    int start_pos;
    int end_pos;
};

struct Candidate{
    int i;
    int j;
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
std::vector<Candidate> _TRUE_UNIQUE_SUBSTRING_POS;

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

//
//  The only information contained in a node is the
//  suffix link. Each suffix in the tree that ends
//  at a particular node can find the next smaller suffix
//  by following the suffix_node link to a new node.  Nodes
//  are stored in a simple array.
//
class Node {
    public :
        int suffix_node;
        Node() { suffix_node = -1; }
        static int Count;
};

//
// This is the hash table where all the currently
// defined edges are stored.  You can dump out
// all the currently defined edges by iterating
// through the table and finding edges whose start_node
// is not -1.
//

Edge Edges[ HASH_TABLE_SIZE ];

//
// The array of defined nodes.  The count is 1 at the
// start because the initial tree has the root node
// defined, with no children.
//

int Node::Count = 1;
Node Nodes[ MAX_LENGTH * 2 ];

//
// Necessary forward references
//
/*
comment out by @rubayet
void validate();
int walk_tree( int start_node, int last_char_so_far );
*/

//
// The default ctor for Edge just sets start_node
// to the invalid value.  This is done to guarantee
// that the hash table is initially filled with unused
// edges.
//

Edge::Edge()
{
    start_node = -1;
}

//
// I create new edges in the program while walking up
// the set of suffixes from the active point to the
// endpoint.  Each time I create a new edge, I also
// add a new node for its end point.  The node entry
// is already present in the Nodes[] array, and its
// suffix node is set to -1 by the default Node() ctor,
// so I don't have to do anything with it at this point.
//

Edge::Edge( int init_first, int init_last, int parent_node )
{
    first_char_index = init_first;
    last_char_index = init_last;
    start_node = parent_node;
    end_node = Node::Count++;
}

//
// Edges are inserted into the hash table using this hashing
// function.
//

int Edge::Hash( int node, int c )
{
    return ( ( node << 8 ) + c ) % HASH_TABLE_SIZE;
}

//
// A given edge gets a copy of itself inserted into the table
// with this function.  It uses a linear probe technique, which
// means in the case of a collision, we just step forward through
// the table until we find the first unused slot.
//

void Edge::Insert()
{
    int i = Hash( start_node, T[ first_char_index ] );
    while ( Edges[ i ].start_node != -1 )
        i = ++i % HASH_TABLE_SIZE;
    Edges[ i ] = *this;
}

//
// Removing an edge from the hash table is a little more tricky.
// You have to worry about creating a gap in the table that will
// make it impossible to find other entries that have been inserted
// using a probe.  Working around this means that after setting
// an edge to be unused, we have to walk ahead in the table,
// filling in gaps until all the elements can be found.
//
// Knuth, Sorting and Searching, Algorithm R, p. 527
//

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

//
// The whole reason for storing edges in a hash table is that it
// makes this function fairly efficient.  When I want to find a
// particular edge leading out of a particular node, I call this
// function.  It locates the edge in the hash table, and returns
// a copy of it.  If the edge isn't found, the edge that is returned
// to the caller will have start_node set to -1, which is the value
// used in the hash table to flag an unused entry.
//

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

//
// When a suffix ends on an implicit node, adding a new character
// means I have to split an existing edge.  This function is called
// to split an edge at the point defined by the Suffix argument.
// The existing edge loses its parent, as well as some of its leading
// characters.  The newly created edge descends from the original
// parent, and now has the existing edge as a child.
//
// Since the existing edge is getting a new parent and starting
// character, its hash table entry will no longer be valid.  That's
// why it gets removed at the start of the function.  After the parent
// and start char have been recalculated, it is re-inserted.
//
// The number of characters stolen from the original node and given
// to the new node is equal to the number of characters in the suffix
// argument, which is last - first + 1;
//

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

//
// This routine prints out the contents of the suffix tree
// at the end of the program by walking through the
// hash table and printing out all used edges.  It
// would be really great if I had some code that will
// print out the tree in a graphical fashion, but I don't!
//

void map_leaf_pos(){
    /*
    Store substring for matching one by one
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
            if (DEBUG_LOG)
                cout << "search string: " << search_string << " end node: " << end_node << ", leaf edge len: " << intermediate_pos_increase << endl;
            _POS_EDGE_LEN_MAPPING.insert(std::pair<int, int>(pos, intermediate_pos_increase-1));
            break;
        case NO_MATCH:
            end_node = -1;
            break;
        
        case PARTIAL_MATCH:
            if (match_pos == search_string.length()){
                if (DEBUG_LOG)
                    cout << "search string: " << search_string << " end node: " << end_node << ", leaf edge len: " << intermediate_pos_increase << endl;
            }
            _POS_EDGE_LEN_MAPPING.insert(std::pair<int, int>(pos, intermediate_pos_increase-1));
        default:
            break;
    }

    return end_node;
}

void find_lsus(){
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
                lsus[index]=T[i];
                index++;
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
                
//                if(DEBUG_LOG)
//                    cout << "substring: " << substring << endl;
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
            
            cout << "unique substring: " << unique_string << endl;
            
            std::map<std::string, Candidate>::iterator it;
            
            for (it=_SUBSTRING_POS_MAPPING.begin(); it != _SUBSTRING_POS_MAPPING.end(); it++) {
                std::string substring = it->first;
                Candidate str_pos = it->second;
                
                if (substring==unique_string){
                    // store the position of the unique string
                    cout << "MUS: i= " << str_pos.i << ", j= " << str_pos.j << endl;
                    
                    _UNIQUE_SUBSTRING_POS.push_back(str_pos);
                }
            }
        }
    }
}

void find_MUS(){
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
            _TRUE_UNIQUE_SUBSTRING_POS.push_back(true_c);
            
            if (DEBUG_LOG)
                cout << "true mus i: " << true_c.i << ", j: "<< true_c.j << endl;
        }
    }
}

void propagate(int i, int j, int k){
    int k_end_pos = _lsus_size[k];
    
    if(k<i || k>j)
        return;
    else if (k_end_pos==N){
        // that means it is null. Thus it was assigned the largest value N
        Candidate k_cand;
        k_cand.i = i;
        k_cand.j = j;
        
        return;
    }
}

void dump_edges( int current_n )
{
    cout << " Start  End  Suf  First Last  String\n";
    for ( int j = 0 ; j < HASH_TABLE_SIZE ; j++ ) {
        Edge *s = Edges + j;
        if ( s->start_node == -1 )
            continue;
        cout << setw( 5 ) << s->start_node << " "
             << setw( 5 ) << s->end_node << " "
             << setw( 3 ) << Nodes[ s->end_node ].suffix_node << " "
             << setw( 5 ) << s->first_char_index << " "
             << setw( 6 ) << s->last_char_index << "  ";
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
                      cout << T[ l ];
                  }
            
        data_box data (start_node, end_node, suffix_node, first_char_index, last_char_index, substring);
        DATA_HUB.push_back(data);
        cout << "\n";
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

//
// This routine constitutes the heart of the algorithm.
// It is called repetitively, once for each of the prefixes
// of the input string.  The prefix in question is denoted
// by the index of its last character.
//
// At each prefix, we start at the active point, and add
// a new edge denoting the new last character, until we
// reach a point where the new edge is not needed due to
// the presence of an existing edge starting with the new
// last character.  This point is the end point.
//
// Luckily for use, the end point just happens to be the
// active point for the next pass through the tree.  All
// we have to do is update it's last_char_index to indicate
// that it has grown by a single character, and then this
// routine can do all its work one more time.
//

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
    cout << "Normally, suffix trees require that the last\n"
         << "character in the input string be unique.  If\n"
         << "you don't do this, your tree will contain\n"
         << "suffixes that don't end in leaf nodes.  This is\n"
         << "often a useful requirement. You can build a tree\n"
         << "in this program without meeting this requirement,\n"
         << "but the validation code will flag it as being an\n"
         << "invalid tree\n\n";
    cout << "Enter string: " << flush;
    cin.getline( T, MAX_LENGTH - 1 );
    N = strlen( T ) - 1;
//
// The active point is the first non-leaf suffix in the
// tree.  We start by setting this to be the empty string
// at node 0.  The AddPrefix() function will update this
// value after every new prefix is added.
//
    Suffix active( 0, 0, -1 );  // The initial active prefix
    for ( int i = 0 ; i <= N ; i++ )
        AddPrefix( active, i );
//
// Once all N prefixes have been added, the resulting table
// of edges is printed out, and a validation step is
// optionally performed.

    /* Added by
     Rubayet */
    
    dump_edges( N );
    map_leaf_pos();
    find_lsus();
    baseline_algorithm();
    unique_substring();
    find_MUS();
    
    /*cout << "Would you like to validate the tree?"
         << flush;
    std::string s;
    getline( cin, s );
    if ( s.size() > 0 && s[ 0 ] == 'Y' || s[ 0 ] == 'y' )
        validate();*/

    return 1;
};

//
// The validation code consists of two routines.  All it does
// is traverse the entire tree.  walk_tree() calls itself
// recursively, building suffix strings up as it goes.  When
// walk_tree() reaches a leaf node, it checks to see if the
// suffix derived from the tree matches the suffix starting
// at the same point in the input text.  If so, it tags that
// suffix as correct in the GoodSuffixes[] array.  When the tree
// has been traversed, every entry in the GoodSuffixes array should
// have a value of 1.
//
// In addition, the BranchCount[] array is updated while the tree is
// walked as well.  Every count in the array has the
// number of child edges emanating from that node.  If the node
// is a leaf node, the value is set to -1.  When the routine
// finishes, every node should be a branch or a leaf.  The number
// of leaf nodes should match the number of suffixes (the length)
// of the input string.  The total number of branches from all
// nodes should match the node count.
//

char CurrentString[ MAX_LENGTH ];
char GoodSuffixes[ MAX_LENGTH ];
char BranchCount[ MAX_LENGTH * 2 ] = { 0 };

/*
Comment out by @rubayet
void validate()
{
    for ( int i = 0 ; i < N ; i++ )
        GoodSuffixes[ i ] = 0;
    walk_tree( 0, 0 );
    int error = 0;
    for ( int i = 0 ; i < N ; i++ )
        if ( GoodSuffixes[ i ] != 1 ) {
            cout << "Suffix " << i << " count wrong!\n";
            error++;
        }
    if ( error == 0 )
        cout << "All Suffixes present!\n";
    int leaf_count = 0;
    int branch_count = 0;
    for ( int i = 0 ; i < Node::Count ; i++ ) {
        if ( BranchCount[ i ] == 0 )
            cout << "Logic error on node "
                 << i
                 << ", not a leaf or internal node!\n";
        else if ( BranchCount[ i ] == -1 )
            leaf_count++;
        else
            branch_count += BranchCount[ i ];
    }
    cout << "Leaf count : "
         << leaf_count
         << ( leaf_count == ( N + 1 ) ? " OK" : " Error!" )
         << "\n";
    cout << "Branch count : "
         << branch_count
         << ( branch_count == (Node::Count - 1) ? " OK" : " Error!" )
         << endl;
}
*/


/*
Comment out by @rubayet
int walk_tree( int start_node, int last_char_so_far )
{
    int edges = 0;
    for ( int i = 0 ; i < 256 ; i++ ) {
        Edge edge = Edge::Find( start_node, i );
        if ( edge.start_node != -1 ) {
            if ( BranchCount[ edge.start_node ] < 0 )
                cerr << "Logic error on node "
                     << edge.start_node
                     << '\n';
            BranchCount[ edge.start_node ]++;
            edges++;
            int l = last_char_so_far;
            for ( int j = edge.first_char_index ; j <= edge.last_char_index ; j++ )
                CurrentString[ l++ ] = T[ j ];
            CurrentString[ l ] = '\0';
            if ( walk_tree( edge.end_node, l ) ) {
                if ( BranchCount[ edge.end_node ] > 0 )
                        cerr << "Logic error on node "
                             << edge.end_node
                             << "\n";
                BranchCount[ edge.end_node ]--;
            }
        }
    }
//
// If this node didn't have any child edges, it means we
// are at a leaf node, and can check on this suffix.  We
// check to see if it matches the input string, then tick
// off it's entry in the GoodSuffixes list.
//
    if ( edges == 0 ) {
        cout << "Suffix : ";
        for ( int m = 0 ; m < last_char_so_far ; m++ )
            cout << CurrentString[ m ];
        cout << "\n";
        GoodSuffixes[ strlen( CurrentString ) - 1 ]++;
        cout << "comparing: " << ( T + N - strlen( CurrentString ) + 1 )
             << " to " << CurrentString << endl;
        if ( strcmp(T + N - strlen(CurrentString) + 1, CurrentString ) != 0 )
            cout << "Comparison failure!\n";
        return 1;
    } else
        return 0;
}
*/
