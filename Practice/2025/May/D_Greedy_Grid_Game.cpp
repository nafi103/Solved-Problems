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
vector<vector<int>>grid;
int dx[] = {0,1};
int dy[] = {1,0};

bool corner(int i, int j){
    return (i==0 and j==m-1) or (i==0 and j==0)  or (i==n-1 and j==0) or (i==n-1 and j==m-1);
}

bool valid(int i, int j){
    return i>=0 and i<n and j>=0 and j<m;
}

pair<int,int> valid_corner(int i, int j){
    int x[] = {1,1,-1,-1};
    int y[] = {1,-1,1,-1};
    for(int k = 0; k<4; k++){
        if(valid(i+x[k], j+y[k])){
            return {i+x[k], j+y[k]};
        }
    }
    return {-1,-1};
}

int dfs(int i, int j, int d, int power){
    if(i==n-1 and j==m-1){
        return grid[i][j];
    }
    if(!valid(i+dx[d],j+dy[d])){
        d^=1;
    }
    int ans = grid[i][j]+dfs(i+dx[d],j+dy[d],d,power);
    if(corner(i,j) and n>1 and m>1 and power){
        auto [ni,nj] = valid_corner(i,j);
        ans = max({ans,grid[i][j]+dfs(ni,nj,0,0),grid[i][j]+dfs(ni,nj,1,0)});
    }
    return ans;
}


void solve()
{
    grid.clear();
    cin>>n>>m;
    grid.resize(n,vector<int>(m));
    int sum = 0;
    for(int i = 0; i<n; i++){
        for(int j = 0; j<m; j++){
            cin>>grid[i][j];
        }
    }
    cout<<max(dfs(0,0,0,1),dfs(0,0,1,1))<<endl;
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
        // google(z);
        solve();
    }
}