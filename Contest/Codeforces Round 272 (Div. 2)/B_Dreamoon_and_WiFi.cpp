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
vector<int>fact(11);

void solve()
{
    string str,given;
    cin>>str>>given;
    int question = count(all(given),'?');
    if(question==0){
        cout<<(count(all(given),'+')==count(all(str),'+')?1:0)<<endl;
        return;
    }
    int need = count(all(str),'+') - count(all(given),'+');
    if(need<0 or need>question){
        cout<<0<<endl;
        return;
    }
    double possible = pow(2,question);
    double valid = fact[question]/(fact[need]*fact[question-need]);
    cout<<valid/possible<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(12);
    cout.setf(ios::fixed);
    int t = 1;
    fact[0] = 1;
    for(int i = 1; i<11; i++)
        fact[i]=(fact[i-1]*i);
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}