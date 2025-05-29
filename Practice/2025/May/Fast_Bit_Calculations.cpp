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
const pair<int,int> dummy = {-1,-1};
int n;
vector<int>v;
vector<vector<vector<pair<int,int>>>>dp;

pair<int,int> operator+(const pair<int,int>&a, const pair<int,int>&b){
    return {a.ff + b.ff,a.ss + b.ss};
}

pair<int,int> f(int i, int prev, int flag){
    if(i>=n){
        return {0,1};
    }
    pair<int,int> &ans = dp[i][prev][flag];
    if(ans!=dummy)
        return ans;
    if(flag){
        ans = f(i+1,1,1);
        if(prev)
            ans.ff+=ans.ss;
        ans = ans + f(i+1,0,1);
    }else{
        if(v[i]){
            ans = f(i+1,1,0);
            if(prev)
                ans.ff+=ans.ss;
            ans = ans + f(i+1,0,1);
        }else{
            ans = f(i+1,0,0);
        }
    }
    return ans;
}

void solve()
{
    dp.clear();
    v.clear();
    cin>>n;
    if(n<=2){
        cout<<0<<endl;
        return;
    }
    while(n){
        v.push_back(n&1);
        n>>=1;
    }
    reverse(all(v));
    n = sz(v);
    dp.assign(n,vector<vector<pair<int,int>>>(2,vector<pair<int,int>>(2,{-1,-1})));
    cout<<f(0,0,0).ff<<endl;
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