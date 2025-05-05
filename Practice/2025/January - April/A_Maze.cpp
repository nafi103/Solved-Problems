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
vector<vector<char>>grid;
int n,m,k;
vector<vector<bool>>visited;
int x[] = {1,-1,0,0};
int y[] = {0,0,1,-1};

bool valid(int i, int j){
    return i>=0 and i<n and j>=0 and j<m and !visited[i][j] and grid[i][j]=='.';
}

void dfs(int i, int j, int l){
    for(int k = 0; k<4; k++){
        if(valid(i+x[k], j+y[k])){
            visited[i+x[k]][j+y[k]] = true;
            dfs(i+x[k],j+y[k],l+1);
        }
    }
    if(k){
        grid[i][j] = 'X';
        k--;
    }
}


void solve()
{
    int sr,sc;
    cin>>n>>m>>k;
    grid.resize(n,vector<char>(m));
    visited.assign(n,vector<bool>(m,false));
    for(int i = 0; i<n; i++){
        for(int j = 0; j<m; j++){
            cin>>grid[i][j];
            if(grid[i][j] =='.'){
                sr = i;
                sc = j;
            }
        }
    }
    visited[sr][sc] = true;
    dfs(sr,sc,0);
    for(int i = 0; i<n; i++){
        for(int j = 0; j<m; j++){
            cout<<grid[i][j];
        }
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
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}