#include <chrono>
#include <condition_variable>
#include <fcntl.h>
#include "fpgaaccessremote.hpp"
#include <arpa/inet.h>
#include <cstdint>
#include <gtest/gtest.h>
#include <mutex>
#include <netinet/in.h>
#include <sys/socket.h>

static int connect_to_server(uint16_t port)
{
	struct sockaddr_in addr;
	addr.sin_family = AF_INET;
	addr.sin_port = htons(port);

	int sockfd = socket(AF_INET, SOCK_STREAM, 0);
	assert(sockfd >= 0);
	assert(inet_pton(AF_INET, "127.0.0.1", &addr.sin_addr) > 0);
	assert(connect(sockfd, (struct sockaddr *)&addr, sizeof(addr)) >= 0);
	usleep(10000);
	return sockfd;
}

TEST(TestFpgaAccessRemote, SetupStartServer)
{
	SetupOptions opts = { .wait_for_connection = false, .port = 1234 };
	FpgaAccessRemote access;

	struct sockaddr_in addr;
	addr.sin_family = AF_INET;
	addr.sin_port = htons(opts.port);

	int sockfd = socket(AF_INET, SOCK_STREAM, 0);
	EXPECT_GE(sockfd, 0);
	EXPECT_GT(inet_pton(AF_INET, "127.0.0.1", &addr.sin_addr), 0);
	EXPECT_LT(connect(sockfd, (struct sockaddr *)&addr, sizeof(addr)), 0);

	access.setup(opts);

	EXPECT_GE(connect(sockfd, (struct sockaddr *)&addr, sizeof(addr)), 0);

	close(sockfd);
}

TEST(TestFpgaAccessRemote, WriteRegister)
{
	SetupOptions opts = { .wait_for_connection = false, .port = 1236 };
	FpgaAccessRemote access;
	access.setup(opts);
	int socket = connect_to_server(opts.port);

	access.write_register(1, 2);

	char msg[50];
	const char *expected = "wr 1 2\n";

	ssize_t bytes = recv(socket, msg, sizeof(msg), MSG_DONTWAIT);
	msg[bytes] = 0;

	EXPECT_EQ(bytes, strlen(expected));
	EXPECT_STREQ(msg, expected);
	close(socket);
}

TEST(TestFpgaAccessRemote, ReadRegister)
{
	SetupOptions opts = { .wait_for_connection = false, .port = 1237 };
	FpgaAccessRemote access;
	access.setup(opts);
	int socket = connect_to_server(opts.port);

	const char *expected = "rd 1\n";
	const char *response = "1 10\n";
	char msg[50];

	//Send the response first else we block
	write(socket, response, strlen(response) + 1);

	EXPECT_EQ(access.read_register(1), 10);

	ssize_t bytes = recv(socket, msg, sizeof(msg), MSG_DONTWAIT);
	msg[bytes] = 0;

	EXPECT_EQ(bytes, strlen(expected));
	EXPECT_STREQ(msg, expected);
	close(socket);
}

static std::string received;

static std::condition_variable handler_called;
static std::mutex handler_called_mutex;

static void handler(const std::string &message)
{
	received = message;
	handler_called.notify_all();
}
TEST(TestFpgaAccessRemote, HandlerIsCalledOnIrq)
{
	SetupOptions opts = { .wait_for_connection = false, .port = 1238 };
	FpgaAccessRemote access;
	access.setup(opts);
	int socket = connect_to_server(opts.port);

	char msg[50];
	const char *expected = "irq my fancy message\n";

	//Test that a null callback doesn't crash the app
	access.set_callback(nullptr);

	write(socket, expected, strlen(expected) + 1);
	sleep(1);

	access.set_callback(handler);

	std::unique_lock<std::mutex> lk(handler_called_mutex);

	write(socket, expected, strlen(expected) + 1);

	EXPECT_EQ(handler_called.wait_for(lk, std::chrono::milliseconds(500)),
		  std::cv_status::no_timeout);

	EXPECT_STREQ(received.data(), expected);

	close(socket);
}

TEST(TestFpgaAccessRemote, EndTestMessageIsSent)
{
	SetupOptions opts = { .wait_for_connection = false, .port = 1235 };
	int socket;
	{
		FpgaAccessRemote access;
		access.setup(opts);
		socket = connect_to_server(opts.port);
		shutdown(socket, SHUT_WR);
		sleep(1);
	}

	const char *expected_message = "end_test\n";
	char msg[50];
	ssize_t bytes = recv(socket, msg, sizeof(msg), MSG_DONTWAIT);
	msg[bytes] = 0;
	EXPECT_EQ(bytes, strlen(expected_message));
	EXPECT_STREQ(msg, expected_message);
	close(socket);
}
