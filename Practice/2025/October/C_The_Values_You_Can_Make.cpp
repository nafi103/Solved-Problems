#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

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

void solve()
{
    int n,k,x;
    cin>>n>>k;
    bool dp[n+1][k+1][k+1], possible[k+1];
    memset(dp,0,sizeof dp);
    memset(possible,0,sizeof possible);
    possible[0] = 1;
    dp[0][0][0] = 1;
    for(int i = 1; i<=n; i++){
        cin>>x;
        for(int sum = 0; sum<=k; sum++){
            for(int subsum = 0; subsum<=sum; subsum++){
                dp[i][sum][subsum]|=dp[i-1][sum][subsum];
                if(sum>=x){
                    dp[i][sum][subsum]|=dp[i-1][sum-x][subsum];
                    if(subsum>=x){
                        dp[i][sum][subsum]|=dp[i-1][sum-x][subsum-x];
                    }
                }
                if(dp[i][sum][subsum] and sum==k)
                    possible[subsum] = true;
            }
        }
    }
    int ans = 0;
    for(int i = 0; i<=k; i++){
        if(possible[i])
            ans++;
    }
    cout<<ans<<endl;
    for(int i = 0; i<=k; i++){
        if(possible[i])
            cout<<i<<" ";
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
        // cout<<"Case "<<z<<": ";
        solve();
    }
}