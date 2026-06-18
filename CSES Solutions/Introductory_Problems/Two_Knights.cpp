#include <bits/stdc++.h>
using namespace std;

#define ll long long
#define mod 1000000007
#define pb push_back
#define fi first
#define se second
#define inf 0x3f3f3f3f
#define MAXN 100005
#define all(x) x.begin(), x.end()
#define rep(i, a, b) for (int i = (a); i < (b); ++i)
#define rev(i, a, b) for (int i = (a); i >= (b); --i)
#define debug(x) cerr << #x << ": " << x << '\n'
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
#define read(x) cin >> x
#define write(x) cout << x << '\n'
#define readv(v)      \
    for (auto &x : v) \
    read(x)
#define writev(v)     \
    for (auto &x : v) \
    write(x)
#define endl '\n'

int main()
{
    fastIO;
    ll n;
    cin >> n;
    cout << "0" << endl;
    for (ll i = 2; i <= n; i++)
    {
        cout << (i * i * (i * i - 1)) / 2 - (4 * (i - 1) * (i - 2)) << endl;
    }
}
