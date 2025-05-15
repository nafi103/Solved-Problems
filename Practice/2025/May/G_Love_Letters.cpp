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
const int N = 100005;
vector<bool>prime(N,true);

void solve()
{
    int n;
    cin>>n;
    vector<int>cnt(26,0);
    for(int i = 0; i<n; i++){
        char c;
        cin>>c;
        cnt[c-'A']++;
    }
    vector<pair<char,int>>ans;
    for(int i = 0; i<26; i++){
        if(prime[cnt[i]]){
            ans.push_back({'A'+i, cnt[i]});
        }
    }
    if(ans.empty()){
        cout<<"Love is painful !"<<endl;
    }else{
        for(auto &[f,s]: ans){
            cout<<f<<" = "<<s<<endl;
        }
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    prime[0] = prime[1] = false;
    for(int i = 2; i*i<N; i++){
        if(prime[i]){
            for(int j = i*i; j<N; j+=i)
                prime[j] = false;
        }
    }
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        cout<<"Case "<<z<<":"<<endl;
        solve();
    }
}