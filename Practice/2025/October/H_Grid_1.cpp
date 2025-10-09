#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 1e9+7;
#define inf 1e18+10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define endl "\n"
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int n,m;
    cin>>n>>m;
    vector<vector<int>>dp(n,vector<int>(m,0));
    dp[n-1][m-1] = 1;
    vector<vector<char>>grid(n,vector<char>(m));
    for(int i = 0; i<n; i++){
        for(int j = 0; j<m; j++){
            cin>>grid[i][j];
        }
    }
    for(int i = n-1; i>=0; i--){
        for(int j = m-1; j>=0; j--){
            if(grid[i][j]=='#')
                continue;
            if(i)
                dp[i-1][j] = (dp[i][j]+dp[i-1][j])%mod;
            if(j)
                dp[i][j-1] = (dp[i][j]+dp[i][j-1])%mod;
        }
    }
    cout<<dp[0][0]<<endl;
}