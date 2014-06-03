from addressbar_handler import AddressBarHandler
from screen_handler import ScreenHandler
from message import MessageHandler

message_handler = MessageHandler()
ScreenHandler(message_handler).start()
AddressBarHandler(message_handler).start()
