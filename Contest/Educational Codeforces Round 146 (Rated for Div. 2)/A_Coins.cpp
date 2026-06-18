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
const double eps = 1e-12;
vector<double>h,t;
vector<vector<double>>dp;
int n;

double f(int i, int j){
    if(i==n)
        return j==0;
    double &ans = dp[i][j];
    if(fabs(ans+1.0)>eps)
        return ans;
    if(j==0)
        return ans = t[i]*f(i+1,j);
    ans=(h[i]*f(i+1,j-1));
    ans+=(t[i]*f(i+1,j));
    return ans;
}

void solve()
{
    cin>>n;
    dp.resize(n,vector<double>((n+1)/2,-1.0));
    h.resize(n);t.resize(n);
    for(int i = 0; i<n; i++){
        cin>>h[i];
        t[i] = 1.0-h[i];
    }
    double less_half = 0;
    for(int i = 0; i<(n+1)/2; i++){
        less_half+=f(0,i);
    }
    cout<<1.0-less_half<<endl;
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