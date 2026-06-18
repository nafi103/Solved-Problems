#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
#define mod 998244353
#define inf 1e18+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define set_bits(x) __builtin_popcount(x)
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
template <class T> using pbds = tree<T, null_type, less_equal<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

bool check(string &a, string &b){
    for(int i = 0; i<7; i++){
        if(a[i]!=b[i] and a[i]!='?') return false;
    }
    return true;
}

void solve()
{
    int n;
    cin>>n;
    string str,make = "abacaba";
    cin>>str;
    int cnt = 0;
    vector<int>possible;
    for(int i = 0; i+6<n; i++){
        string sub = str.substr(i,7);
        if(sub==make) cnt++;
        else if(check(sub,make)) possible.pb(i);
    }
    if(cnt>1 or (!cnt and possible.empty())){
        cout<<"No"<<endl;
        return;
    }
    if(cnt==1){
        cout<<"Yes"<<endl;
        for(auto &x: str){
            if(x=='?') cout<<'z';
            else cout<<x;
        }
        cout<<endl;
        return;
    }
    for(int i = 0; i<sz(possible); i++){
        string newStr = str;
        int idx = possible[i];
        for(int i = idx; i<idx+7; i++){
            newStr[i] = make[i-idx];
        }
        int cnt = 0;
        for(int i = 0; i+6<n; i++){
            string sub = newStr.substr(i,7);
            if(sub==make) cnt++;
        }
        if(cnt==1){
            cout<<"Yes"<<endl;
            for(auto &x: newStr){
                if(x=='?') cout<<'z';
                else cout<<x;
            }
            cout<<endl;
            return;
        }
    }
    cout<<"No"<<endl;
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