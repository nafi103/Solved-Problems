#pragma GCC optimize("O3")
#pragma GCC optimize("Ofast")
#pragma GCC optimize("unroll-loops")
#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
using namespace std;
using namespace __gnu_pbds;
#define ee end()
#define bb begin()
#define ff first
#define ss second
#define int int64_t
#define Int long long
#define vi vector<int>
const int N = 2e5 + 123;
#define pr pair<int, int>
const int mod = 1e9 + 7;
#define vs vector<string>
#define SZ(x) ((int)(x).size())
string cdn[]{"NO", "YES"};
#define NO cout << "NO" << endl;
#define No cout << "No" << endl;
#define no cout << "no" << endl;
#define all(x) x.begin(), x.end()
#define YES cout << "YES" << endl;
#define Yes cout << "Yes" << endl;
#define yes cout << "yes" << endl;
#define sm(a) accumulate(all(a), 0LL)
#define mxe(a) *max_element(all(a)) - a.bb;
#define mne(a) *min_element(all(a)) - a.bb;
#define fr(i, n) for (int i = 0; i < n; i += 1)
#define make_unique(x) \
    sort(all(x));      \
    x.resize(unique(all(x)) - x.begin())
typedef tree<int, null_type, less<int>, rb_tree_tag, tree_order_statistics_node_update> ordered_set;
template <typename T>
istream &operator>>(istream &in, vector<T> &a)
{
    for (auto &x : a)
        in >> x;
    return in;
};
template <typename T>
ostream &operator<<(ostream &out, vector<T> &a)
{
    for (auto &x : a)
        out << x << ' ';
    return out;
};
template <class A, class B>
ostream &operator<<(ostream &out, const pair<A, B> &a) { return out << "(" << a.x << ", " << a.y << ")"; }
#ifndef ONLINE_JUDGE
#define dbg(...) cerr << "[" << #__VA_ARGS__ << "]:", debug_out(__VA_ARGS__)
#else
#define dbg(x)
#endif
void solve()
{
    int n;
    string a, b;
    cin >> n >> a >> b;

    string ans = "";
    ans += b[n - 1];
    int ar = n - 1, br = n - 2;
    while(true){
        if (ar == 0){
            ans += a[ar];
            break;
        }
        else
        {
            if(ans+a[ar] > ans+b[br]){
                ans += b[br];
                br--;
            }else{
                ans += a[ar];
                ar--;
                if(ar < 0){
                    break;
                }
            }
        }
        if(br < 0){
            ans+=a[0];
            break;
        }
        dbg(ans);
    }
    reverse(all(ans));
    cout << ans << '\n';
}
int32_t main()
{
    int tc = 1;
    cin >> tc;
    for (int i = 1; i <= tc; i++)
    {
        // cout << "Case "<<i<<": ";
        solve();
    }
    return 0;
}