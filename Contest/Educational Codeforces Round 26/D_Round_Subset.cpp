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
const int mx = 6400;

void solve()
{
    int n,k,x;
    cin>>n>>k;
    vector<pair<int,int>>num(n,{0,0});
    for(int i = 0; i<n; i++){
        cin>>x;
        while(x%2==0){
            num[i].first++;
            x/=2;
        }
        while(x%5==0){
            num[i].second++;
            x/=5;
        }
    }
    int dp[k+1][mx];
    memset(dp,-1,sizeof dp);
    dp[0][0] = 0;
    for(int i = 0; i<n; i++){
        for(int j = k-1; j>=0; j--){
            for(int l = 0; l+num[i].second<mx; l++){
                if(dp[j][l]!=-1){
                    dp[j+1][l+num[i].second] = max(dp[j+1][l+num[i].second],dp[j][l]+num[i].first);
                }
            }
        }
    }
    int ans = 0;
    for(int i = 0; i<mx; i++){
        ans = max(ans,min(i,dp[k][i]));
    }
    cout<<ans<<endl;
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
        // cout<<"Case "<<z<<": ";
        solve();
    }
}