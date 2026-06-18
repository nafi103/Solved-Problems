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
vector<vector<int>>dp;
vector<int>slime, pref;
int n;

int f(int i, int j){
    int &ans = dp[i][j];
    if(ans!=-1)
        return ans;
    ans = inf;
    for(int k = i; k<j; k++){
        ans = min(ans,f(i,k)+f(k+1,j));
    }
    ans += pref[j]-(i?pref[i-1]:0);
    return ans;
}

void solve()
{
    cin>>n;
    pref.resize(n);
    slime.resize(n);
    for(int i = 0; i<n; i++){
        cin>>slime[i];
        pref[i] = slime[i];
        if(i)
            pref[i]+=pref[i-1];
    }
    dp.resize(n,vector<int>(n,-1));
    for(int i = 0; i<n; i++)
        dp[i][i] = 0;
    cout<<f(0,n-1)<<endl;
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