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
#define inf 1e6+10
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
vector<vector<int>>grid;
vector<vector<vector<int>>>dp;
int n,m;

int dx[] = {1,0};
int dy[] = {0,1};

int f(int x1, int y1, int x2){
    if(x1>=n or x2>=n or y1>=m){
        return -inf;
    }
    int y2 = x1+y1-x2, &ans = dp[x1][y1][x2],mx = -inf;
    if(x1==x2 and y1==y2 and x1==n-1 and y1==m-1){
        return ans = grid[n-1][m-1];
    }
    if((x2>=x1 and y1<=y2) or y2>=m){
        return -inf;
    }
    if(ans!=-1){
        return ans;
    }
    ans = grid[x1][y1] + grid[x2][y2];
    for(int i = 0; i<2; i++){
        for(int j = 0; j<2; j++){
            mx = max(mx, f(x1+dx[i], y1+dy[i], x2+dx[j]));
        }
    }
    ans+=mx;
    return ans;
}

void solve()
{
    grid.clear();
    dp.clear();
    cin>>n>>m;
    grid.resize(n,vector<int>(m));
    for(int i = 0; i<n; i++){
        for(int j = 0; j<m; j++){
            cin>>grid[i][j];
        }
    }
    dp.resize(n,vector<vector<int>>(m,vector<int>(n,-1)));
    cout<<grid[0][0] + f(1,0,0)<<endl;
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