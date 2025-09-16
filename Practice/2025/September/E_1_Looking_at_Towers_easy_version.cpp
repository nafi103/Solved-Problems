#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define ll long long
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
vector<int> v;
int l;
int dp[5000][5000][2];

int f(int i, int j, int found, vector<int>&tower){
    if(j<0)
        return 1;
    if(i<0)
        return 0;
    int &ans = dp[i][j][found];
    if(ans!=-1)
        return ans;
    ans = 0;
    if(found){
        if(v[i]==tower[j]){
            ans = ((ll)ans+f(i-1,j-1,0,tower))%mod;
            ans = ((ll)ans+2ll*f(i-1,j,1,tower))%mod;
        }else{
            if(v[i]<tower[j])
                ans = (2ll*f(i-1,j,1,tower))%mod;
            else
                ans = f(i-1,j,1,tower);
        }
    }else{
        if(v[i]==tower[j]){
            ans = ((ll)ans+f(i-1,j-1,0,tower))%mod;
            ans = ((ll)ans+f(i-1,j,1,tower))%mod;
            ans = ((ll)ans+f(i-1,j,0,tower))%mod;
        }else{
            if(j+1<l and v[i]<tower[j+1] and v[i]<tower[j]){
                ans = (2ll*f(i-1,j,0,tower))%mod;
            }else{
                ans = f(i-1,j,0,tower);
            }
        }
    }
    return ans;
}

void solve()
{
    v.clear();
    int n, ans = 0;
    cin>>n;
    vector<int>L,R;
    v.resize(n);
    readv(v);
    for(int i = n-1; i>=0; i--){
        while(!L.empty() and L.back()<=v[i]){
            L.pop_back();
        }
        L.push_back(v[i]);
    }
    reverse(all(L));
    L.pop_back();
    for(int i = 0; i<n; i++){
        while(!R.empty() and R.back()<=v[i]){
            R.pop_back();
        }
        R.push_back(v[i]);
    }
    for(auto &x: R)
        L.push_back(x);
    l = sz(L);
    for(int i = 0; i<n; i++){
        for(int j = 0; j<l; j++){
            dp[i][j][0] = -1;
            dp[i][j][1] = -1;
        }
    }
    cout<<f(n-1,l-1,0,L)<<endl;
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