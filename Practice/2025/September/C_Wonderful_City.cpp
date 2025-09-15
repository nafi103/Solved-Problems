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
int n;

int f(vector<vector<int>>&grid, vector<int>&cost){
    vector<vector<int>>dp(n,vector<int>(2,inf));
    dp[0][0] = 0;
    dp[0][1] = cost[0];
    for(int i = 1; i<n; i++){
        for(int x = 0; x<2; x++){
            for(int y = 0; y<2; y++){
                bool check = true;
                for(int j = 0; j<n; j++){
                    check &= (grid[i-1][j]+y != grid[i][j]+x);
                }
                if(check){
                    if(x==0){
                        dp[i][x] = min(dp[i][x],dp[i-1][y]);
                    }else{
                        dp[i][x] = min(dp[i][x],dp[i-1][y]+cost[i]);
                    }
                }
            }
        }
    }
    return min(dp[n-1][0],dp[n-1][1]);
}

void transpose(vector<vector<int>>&grid){
    for(int i = 0; i<n; i++){
        for(int j = i+1; j<n; j++){
            swap(grid[i][j],grid[j][i]);
        }
    }
}

void solve()
{
    cin>>n;
    vector<vector<int>>grid(n,vector<int>(n));
    for(int i = 0; i<n; i++){
        for(int j = 0; j<n; j++)
            cin>>grid[i][j];
    }
    vector<int>a(n),b(n);
    readv(a);readv(b);
    int hor_cost = f(grid,a);
    transpose(grid);
    int ver_cost = f(grid,b);
    if(hor_cost+ver_cost<inf)
        cout<<hor_cost+ver_cost<<endl;
    else
        cout<<-1<<endl;
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