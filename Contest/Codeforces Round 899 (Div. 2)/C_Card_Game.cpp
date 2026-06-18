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
    int n;
    char t;
    cin>>n>>t;
    vector<string>card(2*n);
    readv(card);
    map<char,vector<int>>mp;
    for(auto &str: card){
        mp[str[1]].pb(str[0] - '0');
    }
    vector<pair<string,string>>ans;
    for(auto &[f,s]: mp)
        sort(all(s));
    for(auto &[f,v]: mp){
        if(f==t)
            continue;
        if(sz(v)&1){
            if(mp[t].empty()){
                cout<<"IMPOSSIBLE"<<endl;
                return;
            }
            string s1 = "", s2 = "";
            int a1 = v.back();
            v.pop_back();
            int a2 = mp[t].back();
            mp[t].pop_back();
            s1.push_back('0'+a1);
            s2.push_back('0'+a2);
            s1.push_back(f);
            s2.push_back(t);
            ans.push_back({s1,s2});
        }
    }
    if(sz(mp[t])&1){
        cout<<"IMPOSSIBLE"<<endl;
        return;
    }
    for(auto &[f,v]: mp){
        if(v.empty())
            continue;
        for(int i = 0; i<sz(v); i+=2){
            string s1 = "", s2 = "";
            s1.push_back(('0'+v[i]));
            s2.push_back(('0'+v[i+1]));
            s1.push_back(f);
            s2.push_back(f);
            ans.push_back({s1,s2});
        }
    }
    for(auto &[f,s]: ans){
        cout<<f<<" "<<s<<endl;
    }
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