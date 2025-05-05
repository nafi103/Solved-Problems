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
int N;
string str;

void solve()
{
    cin>>N>>str;
    if(N&1){
        no;
        return;
    }else if(N==2){
        if(str[0]==str[1]){
            cout<<"RH"<<endl;
        }
        else no;
        return;
    }
    vector<int>n,s,e,w;
    for(int i = 0; i<N ;i++){
        if(str[i]=='N')
            n.pb(i);
        else if(str[i]=='S')
            s.pb(i);
        else if(str[i]=='E')
            e.pb(i);
        else
            w.pb(i);
    }
    vector<char>ans(N);
    for(int i = 0; sz(n) and sz(s); i++){
        if(i&1){
            ans[n.back()]='R';
            ans[s.back()] = 'R';
        }else{
            ans[n.back()]='H';
            ans[s.back()] = 'H';
        }
        n.pop_back();
        s.pop_back();
    }
    for(int i = 0; sz(e) and sz(w); i++){
        if(i%2==0){
            ans[e.back()]='R';
            ans[w.back()] = 'R';
        }else{
            ans[e.back()]='H';
            ans[w.back()] = 'H';
        }
        e.pop_back();
        w.pop_back();
    }
    if((sz(n)&1) or (sz(s)&1) or (sz(e)&1) or (sz(w)&1)){
        no;
        return;
    }
    if(sz(n)){
        for(int i = 0; i<sz(n); i++){
            if(i%2==0){
                ans[n[i]]='R';
            }else{
                ans[n[i]]='H';
            }
        }
    }
    if(sz(s)){
        for(int i = 0; i<sz(s); i++){
            if(i%2==0){
                ans[s[i]]='R';
            }else{
                ans[s[i]]='H';
            }
        }
    }
    if(sz(e)){
        for(int i = 0; i<sz(e); i++){
            if(i&1){
                ans[e[i]]='R';
            }else{
                ans[e[i]]='H';
            }
        }
    }
    if(sz(w)){
        for(int i = 0; i<sz(w); i++){
            if(i&1){
                ans[w[i]]='R';
            }else{
                ans[w[i]]='H';
            }
        }
    }
    for(auto &x: ans){
        cout<<x;
    }
    cout<<endl;
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