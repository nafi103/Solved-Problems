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
pair<int,int> dummy = {-inf,-inf};
vector<vector<vector<pair<int,int>>>>dp;
vector<int>v;
int n;

template <typename T1, typename T2>
pair<T1, T2>& operator+=(pair<T1, T2>& a, const pair<T1, T2>& b) {
    a.first += b.first;
    a.second += b.second;
    return a;
}

template <typename T1, typename T2>
pair<T1, T2>& operator-=(pair<T1, T2>& a, const pair<T1, T2>& b) {
    a.first -= b.first;
    a.second -= b.second;
    return a;
}

pair<int,int>f(int i, int j, int p){
    if(i>j){
        return {0,0};
    }
    if(i==j){
        if(p==0){
            return {v[i],0};
        }else{
            return {0,v[i]};
        }
    }
    pair<int,int> &ans = dp[i][j][p];
    if(ans!=dummy){
        return ans;
    }
    if(!p){
        ans = {-inf,inf};
        pair<int,int> curr = {0,0};
        for(int k = i; k<=j; k++){
            curr+={v[k],0};
            curr+=f(k+1,j,1);
            if(curr.ff-curr.ss>ans.ff-ans.ss){
                ans = curr;
            }
            curr-=f(k+1,j,1);
        }
        curr = {0,0};
        for(int k = j; k>i; k--){
            curr+={v[k],0};
            curr+=f(i,k-1,1);
            if(curr.ff-curr.ss>ans.ff-ans.ss){
                ans = curr;
            }
            curr-=f(i,k-1,1);
        }
    }else{
        ans = {inf,-inf};
        pair<int,int> curr = {0,0};
        for(int k = i; k<=j; k++){
            curr+={0,v[k]};
            curr+=f(k+1,j,0);
            if(curr.ff-curr.ss<ans.ff-ans.ss){
                ans = curr;
            }
            curr-=f(k+1,j,0);
        }
        curr = {0,0};
        for(int k = j; k>i; k--){
            curr+={0,v[k]};
            curr+=f(i,k-1,0);
            if(curr.ff-curr.ss<ans.ff-ans.ss){
                ans = curr;
            }
            curr-=f(i,k-1,0);
        }
    }
    return ans;
}

void solve()
{
    v.clear();
    dp.clear();
    cin>>n;
    v.resize(n);
    readv(v);
    dp.assign(n,vector<vector<pair<int,int>>>(n,vector<pair<int,int>>(2,dummy)));
    cout<<f(0,n-1,0).ff - f(0,n-1,0).ss<<endl;
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