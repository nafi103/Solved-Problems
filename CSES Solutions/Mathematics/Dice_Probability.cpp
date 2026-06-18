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
vector<vector<double>>dp;  // dp[i][j] -> probability of j at ith throw
const double eps = 1e-8;

double f(int turn, int sum){
    if(turn==0 or sum<1)
        return 0.0;
    if(turn==1){
        return (sum>=1 and sum<=6) ? 1.0/6: 0.0;
    }
    double &ans = dp[turn][sum];
    if(ans+1.0>eps){
        return ans;
    }
    ans = 0.0;
    for(int i = 1; i<=6; i++){
        ans+=f(turn-1,sum-i);
    }
    ans/=6.0;
    return ans;
}

void solve()
{
    int n,a,b;
    cin>>n>>a>>b;
    dp.assign(n+1,vector<double>(b+1,-1.0));
    double ans = 0.0;
    for(int i = a ; i<=b; i++){
        ans+=f(n,i);
    }
    cout<<ans<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(6);
    cout.setf(ios::fixed);
    int t = 1;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}