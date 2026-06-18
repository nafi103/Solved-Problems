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
string a,b;
int n,m;

int f(int i, int j,vector<vector<int>>&dp){
    if(i==n or j==m)
        return 0;
    int &ans = dp[i][j];
    if(ans!=-1)
        return ans;
    if(a[i]==b[j])
        return ans = 1 + f(i+1,j+1,dp);
    return ans = max(f(i+1,j,dp),f(i,j+1,dp));
}


int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    cin>>a>>b;
    n = sz(a); m = sz(b);
    vector<vector<int>>dp(n,vector<int>(m,-1));
    f(0,0,dp);
    int i = 0, j = 0;
    while(i<n and j<m and dp[i][j]){
        if(a[i]==b[j]){
            cout<<a[i];
            i++,j++;
            continue;
        }
        if(i+1<n and dp[i+1][j]==dp[i][j]){
            i++;
        }else{
            j++;
        }
    }
}