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
int n,m;
vector<vector<char>>grid;
vector<vector<bool>>visited;

int dx[] = {0,1,0,-1};
int dy[] = {1,0,-1,0};

bool valid(int i, int j,char &curr){
    return  i>=0 and i<n and j>=0 and j<m and !visited[i][j] and grid[i][j]!=curr;
}

bool inside(int i, int j){
    return  i>=0 and i<n and j>=0 and j<m;
}

void dfs(int i, int j, char &curr){
    visited[i][j] = true;
    for(int p = 0; p<4; p++){
        int ni = i+dx[p], nj = j+dy[p];
        if(valid(ni,nj,curr)){
            dfs(ni,nj,curr);
        }
    }
}

void fill_ouside_of_boundary(char curr){
    visited.clear();
    visited.assign(n,vector<bool>(m,false));
    int i = 0, j = -1, p = 0;
    while(p<4){
        i+=dx[p];
        j+=dy[p];
        if(valid(i,j,curr)){
            dfs(i,j,curr);
        }
        if(!inside(i+dx[p],j+dy[p]))
            p++;
    }
    for(int i = 0; i<n; i++){
        for(int j = 0; j<m; j++){
            if(!visited[i][j])
                grid[i][j] = curr;
        }
    }
}

void solve()
{
    grid.clear();
    cin>>n>>m;
    grid.resize(n,vector<char>(m));
    set<char>s;
    for(int i = 0; i<n; i++){
        for(int j = 0; j<m; j++){
            cin>>grid[i][j];
            if(grid[i][j]!='.')
                s.insert(grid[i][j]);
        }
    }
    for(auto &curr: s){
        fill_ouside_of_boundary(curr);
    }
    for(int i = 0; i<n; i++){
        for(int j = 0; j<m; j++)
            cout<<grid[i][j];
        cout<<endl;
    }
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
        cout<<"Case "<<z<<":\n";
        solve();
    }
}