#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 1e9+7;
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
    int cnt = 0;
    string tstr;
    cin>>tstr;
    vector<int>v;
    v.reserve(sz(tstr));
    for(auto &x: tstr){
        if(x!='a' and x!='b')
            continue;
        if(x=='a'){
            cnt++;
        }else{
            if(cnt){
                v.pb(cnt);
                cnt = 0;
            }
        }
    }
    if(cnt)
        v.pb(cnt);
    if(v.empty()){
        cout<<0<<endl;
        return;
    }
    if(sz(v)==1){
        cout<<v[0]<<endl;
        return;
    }
    int ans = 1;
    for(int i = 0; i<sz(v); i++){
        ans  = (ans*(v[i]+1))%mod;
    }
    cout<<(ans-1+mod)%mod<<endl;
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