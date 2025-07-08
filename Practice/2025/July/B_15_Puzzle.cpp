#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)     \
    for (auto &x : v) \
    cout << x << " "; \
    cout<<endl
#define endl "\n"
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl
#define remove_punctuation(text) regex_replace(text, regex(R"([^\w\s])"), "")
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

char dir[] = {'D', 'L', 'R', 'U'};
int dx[] = {1,0,0,-1};
int dy[] = {0,-1,1,0};
int move_pos[] = {2,0,1,3};

struct Puzzle{
    vector<vector<int>>board;
    int manhattan_sum, blankX, blankY, max_depth;
    string solution;
    Puzzle(){
        board.resize(4,vector<int>(4));
        manhattan_sum = 0;
        solution = "";
    }
    int manhattan_distance(int &i, int &j, int &value){
        return abs((value-1)/4 - i) + abs((value-1)%4 - j);
    }
    void read(){
        for(int i = 0; i<4; i++){
            for(int j = 0; j<4; j++){
                cin>>board[i][j];
                if(board[i][j])
                    manhattan_sum+=manhattan_distance(i,j,board[i][j]);
                else{
                    blankX = i;
                    blankY = j;
                }
            }
        }
    }

    bool valid(int i, int j){
        return i>=0 and i<4 and j>=0 and j<4;
    }

    void swap_tile(int &i, int &j){
        manhattan_sum-=manhattan_distance(i,j,board[i][j]);
        swap(board[i][j], board[blankX][blankY]);
        swap(blankX,i); swap(blankY,j);
        manhattan_sum+=manhattan_distance(i,j,board[i][j]);
    }

    bool solvable() {
        vector<int> flat;
        int rowOfBlank = 0;
        for (int i = 0; i < 4; ++i) {
            for (int j = 0; j < 4; ++j) {
                if (board[i][j] == 0) rowOfBlank = i;
                else flat.push_back(board[i][j]);
            }
        }
        int inversions = 0;
        for (int i = 0; i < sz(flat); ++i)
            for (int j = i + 1; j < sz(flat); ++j)
                if (flat[i] > flat[j]) ++inversions;
        return (inversions + rowOfBlank) % 2 != 0;
    }

    bool dfs(int depth, int last_move){
        if(manhattan_sum==0)
            return true;
        if(depth+manhattan_sum>max_depth)
            return false;
        for(int i = 0; i<4; i++){
            if((last_move^1)==move_pos[i])
                continue;
            int nx = blankX+dx[i], ny = blankY+dy[i];
            if(!valid(nx,ny))
                continue;
            swap_tile(nx,ny);
            solution.push_back(dir[i]);
            if(dfs(depth+1,move_pos[i]))
                return true;
            solution.pop_back();
            swap_tile(nx,ny);
        }
        return false;
    }
    string solve_puzzle(){
        if(!solvable())
            return "This puzzle is not solvable.";
        for(max_depth = 1; max_depth<=35; max_depth++){
            if(dfs(0,-1)){
                return solution;
            }else{
                solution.clear();
            }
        }
        return "This puzzle is not solvable.";
    }
};

void solve()
{
    Puzzle new_puzzle;
    new_puzzle.read();
    cout<<new_puzzle.solve_puzzle()<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        cout<<"Case "<<z<<": ";
        solve();
    }
}