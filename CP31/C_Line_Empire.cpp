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


void solve()
{
    int n,a,b;
    cin>>n>>a>>b;
    vector<int>v(n),move_cost(n),pref(n);
    readv(v);
    pref[0] = v[0];
    move_cost[0] = v[0]*(a+b);
    for(int i = 1; i<n; i++){
        pref[i] = pref[i-1]+v[i];
        move_cost[i] = move_cost[i-1] + (v[i] - v[i-1])*(a+b);
    }
    if(n>1) move_cost[n-1]-=(v[n-1] - v[n-2])*(a);
    else move_cost[0] -= v[0]*a;
    if(a<=b){
        cout<<move_cost[n-1]<<endl;
        return;
    }
    int ans = min(move_cost[n-1],pref[n-1]*b);
    for(int i = 0; i<n-1; i++){
        ans = min(ans,move_cost[i] + ((pref[n-1] - pref[i]) - ((v[i])*(n-1-i)))*b);
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
    cin >> t;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}