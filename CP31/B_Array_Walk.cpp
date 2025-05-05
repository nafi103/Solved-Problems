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
vector<vector<int>>dp;
vector<int>v,pref;

int f(int i, int j, int k){
    if(k==0)
        return v[i];
    if(j==0)
        return dp[i][j] = pref[i+k] - pref[i] + v[i];
    int &ans = dp[i][j];
    if(ans!=0)
        return ans;
    ans = v[i] + f(i+1,j,k-1);
    if(i and j){
        ans = max(ans,v[i]+f(i-1,j-1,k-1));
    }
    return ans;
}


void solve()
{
    dp.clear();
    v.clear();
    pref.clear();
    int n,k,z;
    cin>>n>>k>>z;
    dp.assign(n,vector<int>(z+1,0));
    v.resize(n);
    pref.resize(n);
    readv(v);
    pref[0] = v[0];
    for(int i = 1; i<n; i++){
        pref[i] = v[i]+pref[i-1];
    }
    cout<<f(0,z,k)<<endl;
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
        // google(z);
        solve();
    }
}