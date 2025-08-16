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

int gcd(int a, int b) {
    return b == 0 ? a : gcd(b, a % b);
}

int lcm(int &a, int &b){
    return (a*b)/gcd(a,b);
}

pair<int,int> add(pair<int,int>&a, pair<int,int>b){
    int denom = lcm(a.second,b.second);
    int nom = (denom/a.second)*a.first + (denom/b.second)*b.first;
    int g = gcd(nom,denom);
    nom/=g;
    denom/=g;
    return make_pair(nom,denom);
}

int n,m,dfs_cnt;
vector<vector<bool>>visited;
vector<vector<char>>grid;

int dx[] = {1,-1,0,0};
int dy[] = {0,0,1,-1};

bool valid(int i, int j){
    return i>=0 and i<n and j>=0 and j<m and grid[i][j]=='#' and !visited[i][j];
}

void dfs(int i, int j){
    dfs_cnt++;
    visited[i][j] = true;
    for(int k = 0; k<4; k++){
        int ni = i+dx[k], nj = j+dy[k];
        if(valid(ni,nj))
            dfs(ni,nj);
    }
}

void solve()
{
    visited.clear();
    grid.clear();
    cin>>n>>m;
    visited.assign(n,vector<bool>(m,false));
    grid.assign(n,vector<char>(m));
    for(int i = 0; i<n; i++){
        for(int j = 0; j<m; j++){
            cin>>grid[i][j];
        }
    }
    pair<int,int>ans = {0,1};
    for(int i = 0; i<n; i++){
        for(int j = 0; j<m; j++){
            if(valid(i,j)){
                dfs_cnt = 0;
                dfs(i,j);
                ans = add(ans,make_pair(dfs_cnt*dfs_cnt, n*m));
            }
        }
    }
    if(ans.second==1){
        cout<<ans.first<<endl;
    }else{
        cout<<ans.first<<" / "<<ans.second<<endl;
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
        // cout<<"Case "<<z<<": ";
        solve();
    }
}