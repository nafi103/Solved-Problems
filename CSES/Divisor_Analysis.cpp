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

int expo(int a, int b, int m) {int res = 1; while (b > 0) {if (b & 1)res = (res * a) % m; a = (a * a) % m; b = b >> 1;} return res;}
int mminvprime(int a, int b) {return expo(a, b - 2, b);}

int productOfDivisors(vector<pair<int,int>>&num, int d, int pdiv)
{
    int product = 1;
    for (auto &[p,e] : num) {
        product = (product*expo(p,((e/pdiv)*(d))%(mod-1),mod))%mod;
    }
    return product;
}


void solve()
{
    int n;
    cin>>n;
    int num_div = 1, sum_div = 1, N = 1,prod_div = 1;
    vector<pair<int,int>>num(n);
    bool square = true;
    for(int i = 0; i<n; i++){
        auto &[p,e] = num[i];
        cin>>p>>e;
        N = (N*(expo(p,e,mod)))%mod;
        num_div = (num_div*(e+1))%mod;
        if(square and (e&1)){
            square = false;
            prod_div = (prod_div*((e+1)/2))%(mod-1);
        }else{
            prod_div = (prod_div*(e+1))%(mod-1);
        }
        sum_div = (((sum_div*((expo(p,e+1,mod)-1)%mod))%mod) * (mminvprime(p-1,mod)))%mod;
    }
    cout<<num_div<<" "<<sum_div<<" "<<productOfDivisors(num,prod_div,(square?2:1))<<endl;
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