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
vector<vector<int>>_gcd;
vector<int>v;

int g(int i, int j){
    if(i==j)
        return v[i];
    if(_gcd[i][j]!=0)
        return _gcd[i][j];
    return _gcd[i][j] = gcd(g(i,j-1),v[j]);
}


void solve()
{
    int n;
    cin>>n;
    v.resize(n);
    _gcd.resize(n,vector<int>(n,0));
    readv(v);
    int cnt = count(all(v),1);
    if(cnt){
        cout<<n-cnt<<endl;
        return;
    }
    int mn = INT_MAX;
    for(int i = 0; i<n-1; i++){
        for(int j = i+1; j<n; j++){
            if(g(i,j)==1){
                mn = min(mn,j-i);
            }
        }
    }
    cout<<(mn==INT_MAX?-1: mn+n-1)<<endl;
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
        // google(z);
        solve();
    }
}