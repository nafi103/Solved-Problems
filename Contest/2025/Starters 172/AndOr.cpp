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
    cin>>n;
    vector<int>v(n);
    readv(v);
    set<int> oe, zo;
    for(int i = 0; i<n; i++){
        if(i%2==0 and v[i]) oe.insert(i);
        else if(i&1 and !v[i]) zo.insert(i);
    }
    int q;
    cin>>q;
    while(q--){
        int i,x;
        cin>>i>>x;
        i--;
        if(x==1){
            if(v[i]==0){
                if(i%2==0){
                    oe.insert(i);
                }else{
                    zo.erase(i);
                }
            }
        }else{
            if(v[i]==1){
                if(i%2==0){
                    oe.erase(i);
                }else{
                    zo.insert(i);
                }
            }
        }
        v[i]=x;
        if(i%2==0 and v[i]) oe.insert(i);
        else if(i&1 and !v[i]) zo.insert(i);
        if(oe.empty()) cout<<0<<endl;
        else if(zo.empty()){
            if(sz(oe)) cout<<1<<endl;
            else cout<<0<<endl;
        }else{
            if(*oe.rbegin()>*zo.rbegin())
                cout<<1<<endl;
            else cout<<0<<endl;
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
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}